-- Prove2me | solution 1 for PI.WGL.LTB.bidet_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:09:02.744289+00:00
-- url     : https://prove2.me/submissions/6afcf34b-61ea-4201-a541-b2e3ad52014f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GelfandTsetlinLowering_LiftTupleB
import Theorems.Thm_PI_WGL_LTB_initMinor_std
import Theorems.Thm_PI_WGL_LTB_prod_sz
import Theorems.Thm_PI_WGL_LTB_count_succ
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WGL PI.WGL.LTB
open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial PI.WGL.LTM
namespace PI.WGL.LTB
theorem _root_.solution {n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (ν : Fin n → ℕ) (hsh : shapeDeg sz = ν) :
    bideterminant ℤ sz hsz (stdT sz hsz) = hw ℤ (r := n) le_rfl ν := by
  subst hsh
  unfold bideterminant hw
  let F : ℕ → MvPolynomial (Fin n × Fin n) ℤ := fun y => if hy : y ≤ n then lpMinor ℤ y hy hy else 1
  have h1 : ∀ k, initMinor ℤ (stdT sz hsz k) (hsz k) = F (sz k) := by
    intro k
    have e : F (sz k) = lpMinor ℤ (sz k) (hsz k) (hsz k) := dif_pos (hsz k)
    rw [e]
    exact initMinor_std (hsz k) (hsz k)
  simp only [h1]
  rw [prod_sz sz Finset.univ (n + 1) (fun k _ => Nat.lt_succ_of_le (hsz k)) F, Finset.prod_range_succ']
  have h0 : F 0 = 1 := by
    have e : F 0 = lpMinor ℤ 0 (Nat.zero_le n) (Nat.zero_le n) := dif_pos (Nat.zero_le n)
    rw [e]
    simp [lpMinor]
  rw [h0, one_pow, mul_one, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [count_succ sz hsz s]
  have e : F (s.1 + 1) = lpMinor ℤ (s.1 + 1) (by have := s.2; omega) (by have := s.2; omega) :=
    dif_pos (by have := s.2; omega)
  rw [e]
end PI.WGL.LTB
