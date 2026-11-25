-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_comp_linearEquiv_50ba265b3ab6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:28:51.549799+00:00
-- url     : https://prove2.me/submissions/df3da531-6ecf-4d33-8679-443f41f04b29

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_setAverage_smul_measure_fd7243322d3e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F)
    [ν.IsAddHaarMeasure] (L : E ≃L[ℝ] F) (s : Set F) (g : F → ℝ) :
    ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂ν := by
  have hmap : (map L μ).IsAddHaarMeasure := L.isAddHaarMeasure_map μ
  have hmp : MeasurePreserving L μ (map L μ) := ⟨L.continuous.measurable, rfl⟩
  have he : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have h1 : ⨍ x in L ⁻¹' s, g (L x) ∂μ = ⨍ y in s, g y ∂(map L μ) := by
    rw [setAverage_eq, setAverage_eq, hmp.setIntegral_preimage_emb he, measureReal_def,
      measureReal_def, he.map_apply]
  have h2 : map L μ = addHaarScalarFactor (map L μ) ν • ν := isAddLeftInvariant_eq_smul _ _
  have hpos := addHaarScalarFactor_pos_of_isAddHaarMeasure (map L μ) ν
  rw [h1, h2]
  rw [show (addHaarScalarFactor (map L μ) ν • ν) =
      ((addHaarScalarFactor (map L μ) ν : ENNReal) • ν) from rfl]
  exact setAverage_smul_measure ν (by simpa using hpos.ne') ENNReal.coe_ne_top s g
end GroundTheory.Heights₂.Heights.SphereMean
