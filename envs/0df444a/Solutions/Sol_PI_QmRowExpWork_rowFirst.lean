-- Prove2me | solution 1 for PI.QmRowExpWork.rowFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:13:21.207588+00:00
-- url     : https://prove2.me/submissions/7110ac9a-3cee-4e8e-8cc2-63a41adfdffd

import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowForm
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RowExpansionMinor_FirstColumnSplitBijective
import Theorems.Thm_PI_QmRowExpWork_cycle_perm_zero
import Theorems.Thm_PI_QmRowExpWork_cycle_perm_succ
import Theorems.Thm_PI_QmRowExpWork_sign_cycle_perm
import Theorems.Thm_PI_QmRowExpWork_matrixExtendByZero_zero
import Theorems.Thm_PI_QmRowExpWork_extByZero_succ
import Theorems.Thm_PI_QmRowExpWork_sign_extend_perm
import Theorems.Thm_PI_QmRowExpWork_firstColumnSplit_bijective
import Theorems.Thm_PI_QmRowExpWork_qminorRow_succ

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
    qminorRow E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E (u - (m : ℂ)) (a 0) (b j) * qminorRow E (a ∘ Fin.succ) (b ∘ j.succAbove) u) := by
  rw [qminorRow_succ, ← (firstColumnSplit_bijective m).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [qminorRow, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e : ∀ k : ℕ, u - (m : ℂ) + ((k + 1 : ℕ) : ℂ) = u - (m : ℂ) + 1 + (k : ℂ) := by
    intro k
    push_cast
    ring
  simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm, Units.val_mul, Int.cast_mul,
    List.ofFn_succ, List.prod_cons, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero, extByZero_succ, cycle_perm_succ,
    Fin.val_zero, Nat.cast_zero, add_zero, Fin.val_succ, e, Function.comp_apply]
  rw [mul_assoc]
  congr 1
  rw [← mul_assoc, ← mul_assoc, Int.cast_comm]
end PI.QmRowExpWork
