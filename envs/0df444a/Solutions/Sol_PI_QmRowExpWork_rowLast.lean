-- Prove2me | solution 1 for PI.QmRowExpWork.rowLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:06:59.545811+00:00
-- url     : https://prove2.me/submissions/44a78b3e-1c91-4cec-a8a1-1584e3b0e3ef

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
import Theorems.Thm_PI_QmRowExpWork_qminorRow_succ
import Theorems.Thm_Formalism_REAL_cycleToLast_castSucc
import Theorems.Thm_Formalism_REAL_cycleToLast_last
import Theorems.Thm_Formalism_REAL_extendLast_castSucc
import Theorems.Thm_Formalism_REAL_extendLast_last
import Theorems.Thm_Formalism_REAL_lastColumnSplit_bijective
import Theorems.Thm_Formalism_REAL_sign_cycleToLast
import Theorems.Thm_Formalism_REAL_sign_extendLast


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmRowExpWork
open Formalism.REAL
namespace PI.QmRowExpWork
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m + (j : ℕ)) : ℤ) : A) *
      (qminorRow E (a ∘ Fin.castSucc) (b ∘ j.succAbove) (u - 1) * Tm E u (a (Fin.last m)) (b j)) := by
  rw [qminorRow_succ, ← (lastColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - 1 - (m : ℂ) + 1 + (k : ℂ) = u - (m : ℂ) + (k : ℂ) := by
    intro k
    ring
  have hs : ((-1 : ℤ) ^ (m + (j : ℕ))) = (-1) ^ (m - (j : ℕ)) := by
    have hj : (j : ℕ) ≤ m := Nat.lt_succ_iff.mp j.isLt
    have : m + (j : ℕ) = (m - (j : ℕ)) + 2 * (j : ℕ) := by omega
    rw [this, pow_add, pow_mul]
    simp
  simp only [lastColumnSplit, Equiv.Perm.sign_mul, sign_cycleToLast, sign_extendLast, Units.val_mul, Int.cast_mul,
    List.ofFn_succ', List.prod_concat, Equiv.Perm.mul_apply, extendLast_last, cycleToLast_last,
    extendLast_castSucc, cycleToLast_castSucc, Fin.val_last, Fin.val_castSucc, e, Function.comp_apply,
    sub_add_cancel, hs, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [mul_assoc, mul_assoc]
end PI.QmRowExpWork
