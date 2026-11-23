-- Prove2me | solution 1 for PI.HwUniqW.Hpk_blockW_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:34:40.504404+00:00
-- url     : https://prove2.me/submissions/4f5385ca-a799-41d2-b68e-482df1f48fda

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_blockW_in_out
import Theorems.Thm_PI_HwUniqW_blockW_out
import Theorems.Thm_PI_HwUniqW_piI_in
import Theorems.Thm_PI_HwUniqW_epsI_in
import Theorems.Thm_PI_HwUniqW_piI_out
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
noncomputable section
namespace PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
private lemma Hpk_apply_wp_eq_ite (i l : Fin (2 * r + k + 1)) :
    Hpk k r i l = if l = piI k r i then epsI k r i else 0 := by
  have hi := i.isLt
  have hl := l.isLt
  simp only [Hpk, piI, epsI, Fin.ext_iff]
  split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num
private lemma Hpk_apply_eq_ite_piI (l j : Fin (2 * r + k + 1)) :
    Hpk k r l j = if l = piI k r j then epsI k r j else 0 := by
  have hj := j.isLt
  have hl := l.isLt
  simp only [Hpk, piI, epsI, Fin.ext_iff]
  split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num
private lemma mul_Hpk_apply_highest_weight_uniqueness (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (M * Hpk k r) i j = M i (piI k r j) * epsI k r j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r j)]
  · rw [Hpk_apply_eq_ite_piI, if_pos rfl]
  · intro l _ hl
    rw [Hpk_apply_eq_ite_piI, if_neg hl, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h
private lemma Hpk_mul_applyHighestWeightUniqueness (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * M) i j = epsI k r i * M (piI k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
  · rw [Hpk_apply_wp_eq_ite, if_pos rfl]
  · intro l _ hl
    rw [Hpk_apply_wp_eq_ite, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.HwUniqW
end
end

set_option autoImplicit false
open Matrix
noncomputable section
open PI PI.HwUniqW
open PI.UpqRep
variable {k r : ℕ}
namespace PI.HwUniqW
theorem _root_.solution (a : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * blockW k r a = blockW k r a * Hpk k r := by
  ext i j
  rw [Hpk_mul_applyHighestWeightUniqueness, mul_Hpk_apply_highest_weight_uniqueness]
  by_cases hi : InB k r i
  · rw [piI_in hi, epsI_in hi, one_mul]
    by_cases hj : InB k r j
    · rw [piI_in hj, epsI_in hj, mul_one]
    · rw [blockW_in_out a hi hj, blockW_in_out a hi (piI_out hj), zero_mul]
  · rw [blockW_out a hi, blockW_out a (piI_out hi)]
    have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
    have h1 := i.isLt
    have h2 := j.isLt
    simp only [piI, epsI, Fin.ext_iff]
    split_ifs <;> (try dsimp only at *) <;> first | rfl | (exfalso; omega) | norm_num
end PI.HwUniqW
