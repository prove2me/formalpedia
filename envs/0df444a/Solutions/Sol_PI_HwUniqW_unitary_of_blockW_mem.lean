-- Prove2me | solution 1 for PI.HwUniqW.unitary_of_blockW_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:43.278845+00:00
-- url     : https://prove2.me/submissions/c81dda10-f89f-453d-a719-b2ba5a420b46

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_HpkMulMulHpkApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_UnitaryOfBlockWMem
import Theorems.Thm_PI_HwUniqW_inB_bl
import Theorems.Thm_PI_HwUniqW_blockIndex_injective
import Theorems.Thm_PI_HwUniqW_blockW_bl
import Theorems.Thm_PI_HwUniqW_blockW_mul
import Theorems.Thm_PI_HwUniqW_blockW_conjTranspose
import Theorems.Thm_PI_HwUniqW_piI_in
import Theorems.Thm_PI_HwUniqW_epsI_in
import Theorems.Thm_PI_HwUniqW_Hpk_blockW_comm
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
theorem _root_.solution {h : Matrix (Fin k) (Fin k) ℂ} (hm : blockW k r h ∈ UH (Hpk k r)) :
    hᴴ * h = 1 := by
  have h0 : (blockW k r h)ᴴ * Hpk k r * blockW k r h = Hpk k r := hm
  rw [mul_assoc, Hpk_blockW_comm, ← mul_assoc, blockW_conjTranspose, blockW_mul] at h0
  ext a b
  have e := congrFun (congrFun h0 (bl k r a)) (bl k r b)
  rw [mul_Hpk_apply_highest_weight_uniqueness, Hpk_apply_wp_eq_ite, piI_in (inB_bl b), epsI_in (inB_bl b), mul_one, blockW_bl,
    piI_in (inB_bl a), epsI_in (inB_bl a)] at e
  rw [e, Matrix.one_apply]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab, if_neg (fun e' => hab (blockIndex_injective e').symm)]
end PI.HwUniqW
