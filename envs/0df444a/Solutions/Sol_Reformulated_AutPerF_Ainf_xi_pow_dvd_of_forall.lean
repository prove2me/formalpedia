-- Prove2me | solution 1 for Reformulated.AutPerF.Ainf.xi_pow_dvd_of_forall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:28:23.960385+00:00
-- url     : https://prove2.me/submissions/1192aceb-64eb-4c27-8aeb-8aab98732ad2

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_Kernel
import Theorems.Thm_Reformulated_AutPerF_eq_zero_of_forall_pow_dvd
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_xi
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_ne_zero
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_Ainf_xi_dvd_of_dvd_p_pow_mul
import Theorems.Thm_Reformulated_AutPerF_BdRPlus_theta_eq_zero_iff
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


attribute [local simp] Reformulated.AutPerF.Ainf.theta_xi

set_option autoImplicit false
noncomputable section
open Ideal
open Reformulated Reformulated.AutPerF
universe u
variable {p : ℕ} [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
open Reformulated.AutPerF.Ainf
variable [IsDomain R]
variable [ValuationRing R]
variable [CharZero R]
namespace Reformulated.AutPerF.Ainf
theorem _root_.solution (ϖ : PFlat p R) {n : ℕ} {x : Ainf p R}
    (h : ∀ k : ℕ, ∃ a b, x = (p : Ainf p R) ^ k * a + xi ϖ ^ n * b) : xi ϖ ^ n ∣ x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have h0 : theta p R x = 0 := eq_zero_of_forall_pow_dvd (p : R) fun k => by
      obtain ⟨a, b, e⟩ := h k
      exact ⟨theta p R a, by rw [e]; simp⟩
    obtain ⟨y, rfl⟩ := (theta_eq_zero_iff ϖ x).1 h0
    rw [pow_succ']
    refine mul_dvd_mul_left _ (ih fun k => ?_)
    obtain ⟨a, b, e⟩ := h k
    obtain ⟨a', rfl⟩ : xi ϖ ∣ a := xi_dvd_of_dvd_p_pow_mul ϖ (k := k)
      ⟨y - xi ϖ ^ n * b, by linear_combination -e⟩
    exact ⟨a', b, mul_left_cancel₀ (xi_ne_zero ϖ) (by linear_combination e)⟩
end Reformulated.AutPerF.Ainf
