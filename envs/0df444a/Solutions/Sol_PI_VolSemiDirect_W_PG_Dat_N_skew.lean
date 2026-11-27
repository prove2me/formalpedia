-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.N_skew
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:42.043667+00:00
-- url     : https://prove2.me/submissions/430fe78e-c418-47d4-941e-31434315bfbd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_f_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_f
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_f
import Theorems.Thm_P2M_PI_VolSemiDirect_W_PG_Dat_N_f__c785d52daa49
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_W_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_add_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_mem_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable {D : Dat A n r}
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) (a b : Fin r) :
    D.h (D.f a) (S (D.f b)) + D.σA (D.h (D.f b) (S (D.f a))) +
      D.h (D.pW (S (D.f a))) (D.pW (S (D.f b))) = 0 := by
  have h0 : D.h (S (D.f a)) (S (D.f b)) = 0 := by rw [hU (D.f a) (D.f b)]; exact H.ff a b
  have hWa := isW_pW H (S (D.f a))
  have hWb : (∀ c, D.h (D.e c) (D.pW (S (D.f b))) = 0) ∧
      (∀ c, D.h (D.f c) (D.pW (S (D.f b))) = 0) ∧ D.h D.z (D.pW (S (D.f b))) = 0 :=
    isW_pW H _
  rw [N_f' H hS hU a, N_f' H hS hU b] at h0
  simp only [h_add_left, h_add_right] at h0
  rw [H.ff a b, hWb.2.1 a, h_f_pX H a, h_W_f H hWa b,
    h_W_span H hWa (pX_mem_span (S (D.f b))), h_pX_f H b, h_pX_left hWb.1,
    h_pX_left (fun c => h_e_pX H c (S (D.f b)))] at h0
  linear_combination h0
end PI.VolSemiDirect.W.PG.Dat
