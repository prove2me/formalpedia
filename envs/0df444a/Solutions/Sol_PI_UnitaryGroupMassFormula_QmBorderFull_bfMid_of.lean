-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.bfMid_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:16:53.135124+00:00
-- url     : https://prove2.me/submissions/8334c58c-23f9-42fb-a198-a51d86374dcc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_comp_skip1
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bS_castSucc
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_bS_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rowE
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rw_zero
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rw_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rows_succ
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_rows_last
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_cmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_tm_comm_E


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution (hLC : ExpLastCol) (hLR : ExpLastRow) (hX : BFCross) : BFMid := by
  intro A _ _ n m E e es v hE hB u w
  cases m with
  | zero => exact w.elim0
  | succ k =>
  have hv : ∀ x, v x ≠ e := hB.2.2.1
  have hves : ∀ x, v x ≠ es := hB.2.2.2
  have hL : bE e (bS v es) w.castSucc.succ = v w := by simp [bE, bS]
  have hT : Tm E u (v w) e = E (v w) e := by simp [Tm, hv w]
  rw [hL, show bE e (bS v es) 0 = e from rfl, hT, show bE e (bS v es) ∘ Fin.succ = bS v es from rfl]
  rw [hLC A n (k + 1) E _ (bS v es) (u - 1), Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  simp only [bS_castSucc, bS_last]
  rw [hX A n k E e es v hE hB u w]
  simp only [Fin.succAbove_zero, Fin.succ_last, rw_zero, rw_last, rows_last]
  rw [rows_succ e es v w (by omega), rowE hLR E hE e (v ∘ w.succAbove) v hv (u - 1)]
  simp only [comp_skip1]
  have hTe : Tm E (u - 1 - ((k + 1 : ℕ) : ℂ)) e es = E e es := by simp [Tm, hB.2.1]
  have hu2 : u - 1 - 1 = u - 2 := by ring
  have hu3 : u - 1 - ((k + 1 : ℕ) : ℂ) = u - ((k + 1 : ℕ) : ℂ) - 1 := by ring
  rw [hTe, hu2, hu3]
  have hcomm : ∀ x, E e (v x) * Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es =
      Tm E (u - ((k + 1 : ℕ) : ℂ) - 1) es es * E e (v x) := fun x =>
    (tm_comm_E E hE _ es e (v x) hB.2.1.symm (hves x)).symm
  have he2 : ((-1 : ℤ) ^ (k + 1 + (k + 1))) = 1 := Even.neg_one_pow ⟨k + 1, rfl⟩
  have p0 : ∀ Q : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (k + 1) : ℤ) : A) * (Q * E e es)))
      = (((-1 : ℤ) ^ ((w : ℕ) + 1 + (k + 1)) : ℤ) : A) * (E (v w) e * (Q * E e es)) := by
    intro Q; rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add]
  have pm : ∀ S : A, (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ((((-1 : ℤ) ^ (w : ℕ) : ℤ) : A) * S))
      = -(E (v w) e * S) := by
    intro S
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add, Odd.neg_one_pow ⟨w, by ring⟩, Int.cast_neg, Int.cast_one,
      neg_one_mul]
  have pl : ∀ f : Fin (k + 1) → A,
      (((-1 : ℤ) ^ ((w : ℕ) + 1) : ℤ) : A) * (E (v w) e * ∑ x : Fin (k + 1), (((-1 : ℤ) ^ (x : ℕ) : ℤ) : A) * f x)
      = -∑ x : Fin (k + 1), (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) * (E (v w) e * f x) := by
    intro f
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [cmul, ← mul_assoc, ← Int.cast_mul, ← pow_add,
      show ((-1 : ℤ) ^ ((w : ℕ) + 1 + (x : ℕ))) = -(-1) ^ ((w : ℕ) + (x : ℕ)) by ring, Int.cast_neg, neg_mul]
  simp only [Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last, add_zero, Nat.succ_eq_add_one, he2,
    Int.cast_one, one_mul, Finset.sum_mul, mul_assoc, hcomm, mul_add]
  simp only [p0, pm, pl]
  simp only [Finset.mul_sum, mul_ite, mul_zero, cmul]
  abel
end PI.UnitaryGroupMassFormula.QmBorderFull
