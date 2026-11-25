-- Prove2me | solution 1 for PI.FrameInd.NegB.eq_zero_of_negMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:34.546454+00:00
-- url     : https://prove2.me/submissions/efdbcd4d-29ad-4125-bb61-d5c89f937ad9

import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FrameInduction_EqZeroOfNegMap
import Theorems.Thm_PI_FrameInd_NegB_re_herm
import Theorems.Thm_PI_FrameInd_NegB_Pk_inj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic
noncomputable section
open PI PI.FrameInd PI.FrameInd.NegB
namespace PI.FrameInd.NegB
theorem _root_.solution (k r : ℕ) (x : Fin (2 * r + k + 1) → ℂ) (hx : negMap k r x = 0)
    (hre : (herm (Hpk k r) x x).re ≤ 0) : x = 0 := by
  apply Pk_inj k r x
  have hneg : ∀ i : Fin (2 * r + k + 1), ¬ i.val < r + k → (Pk k r *ᵥ x) i = 0 := by
    intro i hi
    have h1 := congrFun hx ⟨i.val - (r + k), by omega⟩
    simp only [negMap, LinearMap.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
      Pi.zero_apply] at h1
    have h2 : (⟨r + k + (i.val - (r + k)), by omega⟩ : Fin (2 * r + k + 1)) = i := by
      ext
      simp only
      omega
    rw [h2] at h1
    exact h1
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ (if i.val < r + k then (1 : ℝ) else -1) *
      Complex.normSq ((Pk k r *ᵥ x) i) := by
    intro i _
    by_cases h : i.val < r + k
    · rw [if_pos h, one_mul]
      exact Complex.normSq_nonneg _
    · rw [if_neg h, hneg i h, map_zero, mul_zero]
  have hsum := re_herm k r x
  have hzero : ∑ i, (if i.val < r + k then (1 : ℝ) else -1) * Complex.normSq ((Pk k r *ᵥ x) i) = 0 :=
    le_antisymm (hsum ▸ hre) (Finset.sum_nonneg hterm)
  ext i
  by_cases h : i.val < r + k
  · have h1 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    rw [if_pos h, one_mul] at h1
    simpa using Complex.normSq_eq_zero.mp h1
  · simpa using hneg i h
end PI.FrameInd.NegB
