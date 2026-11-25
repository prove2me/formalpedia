-- Prove2me | solution 1 for PI.HwUniqW.fix_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:43:12.553029+00:00
-- url     : https://prove2.me/submissions/135339af-da2a-4b38-93da-ff27528185ab

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_ne_of_inB
import Theorems.Thm_PI_HwUniqW_piI_out
import Theorems.Thm_PI_HwUniqW_fix_col
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
private lemma Hpk_mul_applyHighestWeightUniqueness (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (i j : Fin (2 * r + k + 1)) : (Hpk k r * M) i j = epsI k r i * M (piI k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (piI k r i)]
  · rw [Hpk_apply_wp_eq_ite, if_pos rfl]
  · intro l _ hl
    rw [Hpk_apply_wp_eq_ite, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
private lemma piI_piI_highest_weight_uniqueness (i : Fin (2 * r + k + 1)) : piI k r (piI k r i) = i := by
  have hi := i.isLt
  apply Fin.ext
  simp only [piI]
  split_ifs <;> (try dsimp only at *) <;> omega
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
theorem _root_.solution {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hU : m ∈ UH (Hpk k r))
    (hm : FixEW k r m) (i j : Fin (2 * r + k + 1)) (hi : ¬ InB k r i) (hj : InB k r j) : m i j = 0 := by
  have hU' : mᴴ * Hpk k r * m = Hpk k r := hU
  have hpo : ¬ InB k r (piI k r i) := piI_out hi
  have e := congrFun (congrFun hU' (piI k r i)) j
  rw [mul_assoc, Matrix.mul_apply, Finset.sum_eq_single (piI k r i)] at e
  · rw [Matrix.conjTranspose_apply, fix_col hm _ hpo, if_pos rfl, star_one, one_mul, Hpk_mul_applyHighestWeightUniqueness,
      Hpk_apply_wp_eq_ite, piI_piI_highest_weight_uniqueness, if_neg (ne_of_inB hj hi)] at e
    have hne : epsI k r (piI k r i) ≠ 0 := by
      unfold epsI
      split_ifs <;> norm_num
    exact (mul_eq_zero.mp e).resolve_left hne
  · intro l _ hl
    rw [Matrix.conjTranspose_apply, fix_col hm _ hpo, if_neg hl, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h
end PI.HwUniqW
