-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_pos_hausdorffMeasure_image_le_of_not_injective_b03f868ef36e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:15:15.531702+00:00
-- url     : https://prove2.me/submissions/28930952-e756-4bbb-9859-9804e249246d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker_aaa68814a6b5

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (f : (ι → ℝ) → F)
    (A : (ι → ℝ) →L[ℝ] F) (hA : ¬ Function.Injective A) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ δ : ℝ≥0, 0 < δ ∧ ∀ t : Set (ι → ℝ), ApproximatesLinearOn f A t δ →
      μH[Fintype.card ι] (f '' t) ≤ ε * volume t := by
  obtain ⟨a, b, hab, hne⟩ : ∃ a b, A a = A b ∧ a ≠ b := by
    simpa [Function.Injective, not_forall] using hA
  have hk0 : a - b ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨i0, hi0⟩ : ∃ i0, (a - b) i0 ≠ 0 := by
    simpa using Function.ne_iff.mp hk0
  set k : ι → ℝ := ((a - b) i0)⁻¹ • (a - b) with hkdef
  have hk : A k = 0 := by rw [hkdef, map_smul, map_sub, hab, sub_self, smul_zero]
  have hki : k i0 = 1 := by
    rw [hkdef, Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hi0
  set K : ℝ≥0 := Real.toNNReal (‖A‖ + 1 + ‖k‖)
  set δ : ℝ≥0 := min 1 (ε / (K ^ Fintype.card ι + 1))
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hε (by positivity))
  refine ⟨δ, hδ0, fun t ht => ?_⟩
  have key :=
    hausdorffMeasure_image_le_of_approximatesLinearOn_of_mem_ker hk hki hδ0 (min_le_left _ _) ht
  refine key.trans ?_
  have hKδ : K ^ Fintype.card ι * δ ≤ ε := by
    calc K ^ Fintype.card ι * δ ≤ (K ^ Fintype.card ι + 1) * (ε / (K ^ Fintype.card ι + 1)) := by
          gcongr
          · exact le_self_add
          · exact min_le_right _ _
      _ = ε := by
        rw [mul_div_assoc']
        exact mul_div_cancel_left₀ ε (by positivity)
  have hcoe : (K : ℝ≥0∞) ^ (Fintype.card ι : ℝ) * ENNReal.ofReal δ =
      ((K ^ Fintype.card ι * δ : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.rpow_natCast, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul, ENNReal.coe_pow]
  rw [hcoe]
  gcongr
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
