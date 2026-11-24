-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_not_isUnitAt_mul_260a18dd0eb1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:55:53.902199+00:00
-- url     : https://prove2.me/submissions/06f7c779-702d-4cb9-8a7c-a6e1cb0149e6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointUnitSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_exists_max_317237edee38
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_le_of_mem_add946ce0df5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ClosedPointUnitSectionAlt_isUnitAt_iff_3571b1996383

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
open ReciprocityTheory.ChartRestriction.G.Geo NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
variable [NumberField K']
namespace GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) {P : HeightOneSpectrum (𝓞 K')} {a b : ℕ}
    {g h : K'} (hg : ¬IsUnitAt y P a g) (hh : h ∈ chartLat y 1 b) : ¬IsUnitAt y P (a + b) (g * h) := by
  obtain ⟨t, ht0, ht⟩ := exists_max y hy P
  rw [isUnitAt_iff y ht, not_le] at hg ⊢
  rw [map_mul, pow_add]
  have hb := le_of_mem y ht0 ht hh
  have hpos : 0 < P.valuation K' (y ⟨(), t⟩) ^ b :=
    zero_lt_iff.mpr (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr ht0))
  calc P.valuation K' g * P.valuation K' h ≤ P.valuation K' g * P.valuation K' (y ⟨(), t⟩) ^ b :=
        mul_le_mul' le_rfl hb
    _ < P.valuation K' (y ⟨(), t⟩) ^ a * P.valuation K' (y ⟨(), t⟩) ^ b :=
        mul_lt_mul_of_pos_right hg hpos
end GroundTheory.Heights₂.Heights.ClosedPointUnitSectionAlt
