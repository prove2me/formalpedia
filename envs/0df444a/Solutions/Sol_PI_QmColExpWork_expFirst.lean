-- Prove2me | solution 1 for PI.QmColExpWork.expFirst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:12.772879+00:00
-- url     : https://prove2.me/submissions/e3c8e980-41d9-428a-b4d1-802527728162

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
import Theorems.Thm_PI_QmColExpWork_cycle_perm_zero
import Theorems.Thm_PI_QmColExpWork_cycle_perm_succ
import Theorems.Thm_PI_QmColExpWork_sign_cycle_perm
import Theorems.Thm_PI_QmColExpWork_matrixExtendByZero_zero
import Theorems.Thm_PI_QmColExpWork_extByZero_succ
import Theorems.Thm_PI_QmColExpWork_sign_extend_perm
import Theorems.Thm_PI_QmColExpWork_firstColumnSplit_bijective

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
open PI PI.QmColExpWork
open Formalism.REAL
namespace PI.QmColExpWork
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin (m + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (j : ℕ) : ℤ) : A) *
      (Tm E u (a j) (b 0) * qminor E (a ∘ j.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold qminor
  conv_lhs => rw [← (firstColumnSplit_bijective m).sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hs : Equiv.Perm.sign (phi0 m (j, τ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign τ := by
    simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm]
  have h0 : phi0 m (j, τ) 0 = j := by
    simp only [phi0, Equiv.Perm.mul_apply, matrixExtendByZero_zero, cycle_perm_zero]
  have hk : ∀ k : Fin m, phi0 m (j, τ) k.succ = j.succAbove (τ k) := by
    intro k
    simp only [phi0, Equiv.Perm.mul_apply, extByZero_succ, cycle_perm_succ]
  have hu : ∀ k : Fin m, u - (((k.succ : Fin (m + 1)) : ℕ) : ℂ) = u - 1 - ((k : ℕ) : ℂ) := by
    intro k
    rw [Fin.val_succ, Nat.cast_succ]
    ring
  simp only [hs, List.ofFn_succ, List.prod_cons, h0, hk, hu, Function.comp_apply,
    Fin.val_zero, Nat.cast_zero, sub_zero]
  simp only [← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  first
  | (push_cast; ring)
  | push_cast
  | simp
end PI.QmColExpWork
