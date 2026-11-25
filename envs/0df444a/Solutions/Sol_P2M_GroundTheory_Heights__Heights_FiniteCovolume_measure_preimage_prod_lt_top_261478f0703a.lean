-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_lt_top_261478f0703a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:14:17.830266+00:00
-- url     : https://prove2.me/submissions/34c8bb45-f16c-45ba-b8b1-089282cfd530

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsDoubleCoset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PDoubleCosetCovolume
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_measure_preimage_prod_le_8d2712d18583
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_sliceMeasure_eq_smul_haar_b8209152515f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Topology Set
open scoped ENNReal NNReal Pointwise
set_option linter.unusedSectionVars false
noncomputable section
variable {G G₁ G₂ : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁]
  [MeasurableSpace G₁] [BorelSpace G₁] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂]
variable {Φ : G ≃ₜ* G₁ × G₂} {μ : Measure G} {V : Set G₂}
variable [LocallyCompactSpace G₁] [T2Space G₁] [SecondCountableTopology G₁] [μ.IsHaarMeasure]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
theorem _root_.solution (hV : IsOpen V) (hVc : IsCompact V) {A : Set G₁}
    (hA : (Measure.haar : Measure G₁) A < ∞) : μ (Φ ⁻¹' (A ×ˢ V)) < ∞ := by
  refine (measure_preimage_prod_le hV A).trans_lt ?_
  obtain ⟨c, hc⟩ := sliceMeasure_eq_smul_haar (Φ := Φ) (μ := μ) hV hVc
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hA
end GroundTheory.Heights₂.Heights.FiniteCovolume
