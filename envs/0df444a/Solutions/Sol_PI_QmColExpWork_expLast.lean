-- Prove2me | solution 1 for PI.QmColExpWork.expLast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:06:50.486529+00:00
-- url     : https://prove2.me/submissions/ec7dc5e8-92e7-4c19-953b-b1219d93a049

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
    qminor E a b u = ∑ j : Fin (m + 1), (((-1 : ℤ) ^ (m + (j : ℕ)) : ℤ) : A) *
      (qminor E (a ∘ j.succAbove) (b ∘ Fin.castSucc) u * Tm E (u - (m : ℂ)) (a j) (b (Fin.last m))) := by
  unfold qminor
  have hr : ∀ k : Fin m, finRotate (m + 1) k.castSucc = k.succ := by
    intro k
    first
    | exact finRotate_castSucc k
    | exact Fin.ext (by rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last k).ne, Fin.coe_castSucc, Fin.val_succ])
  have hbij : Function.Bijective
      (fun p : Fin (m + 1) × Equiv.Perm (Fin m) => phi0 m p * finRotate (m + 1)) :=
    (Equiv.mulRight (finRotate (m + 1))).bijective.comp (firstColumnSplit_bijective m)
  conv_lhs => rw [← hbij.sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hs : Equiv.Perm.sign (phi0 m (j, τ) * finRotate (m + 1)) =
      (-1) ^ (j : ℕ) * Equiv.Perm.sign τ * (-1) ^ m := by
    clear hr hbij
    have h1 : Equiv.Perm.sign (phi0 m (j, τ)) = (-1) ^ (j : ℕ) * Equiv.Perm.sign τ := by
      simp only [phi0, Equiv.Perm.sign_mul, sign_cycle_perm, sign_extend_perm]
    rw [Equiv.Perm.sign_mul, h1, sign_finRotate]
    all_goals first | rfl | exact rfl | simp [mul_comm, mul_left_comm, mul_assoc]
  have hl : (phi0 m (j, τ) * finRotate (m + 1)) (Fin.last m) = j := by
    simp only [Equiv.Perm.mul_apply, finRotate_last, phi0, matrixExtendByZero_zero, cycle_perm_zero]
  have hk : ∀ k : Fin m, (phi0 m (j, τ) * finRotate (m + 1)) k.castSucc = j.succAbove (τ k) := by
    intro k
    simp only [Equiv.Perm.mul_apply, hr, phi0, extByZero_succ, cycle_perm_succ]
  simp only [hs, List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_cons,
    List.prod_nil, mul_one, hl, hk, Function.comp_apply, Fin.val_last, Fin.coe_castSucc]
  simp only [← zsmul_eq_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  first
  | (push_cast; ring)
  | push_cast
  | simp
end PI.QmColExpWork
