-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.pW_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:18:30.716014+00:00
-- url     : https://prove2.me/submissions/29ab8fff-a669-4bfc-a9bc-674272ae60e5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_complement_proj_image
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pz_apply


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
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.pW (S v) = S (D.pW v) := by
  have hS' : (∀ a, S (D.e a) = D.e a) ∧ S D.z = D.z := hS
  have hfix : ∀ x, S (D.pU x) = D.pU x := by
    intro x
    rw [pU_apply, pX_apply, pXv_apply, pz_apply]
    simp only [map_add, map_sum, map_smul, hS'.1, hf, hS'.2]
  have hwW : ∀ u, IsW D u → D.pW (S u) = S u := by
    intro u hu
    have hu' : (∀ a, D.h (D.e a) u = 0) ∧ (∀ a, D.h (D.f a) u = 0) ∧ D.h D.z u = 0 := hu
    have h0 : ∀ a, D.h (D.f a) (S u) = 0 := fun a => by
      rw [← hf a, hU (D.f a) u]; exact hu'.2.1 a
    rw [complement_proj_image hS hU hu, pX_apply]
    simp [h0]
  have hv : v = D.pU v + D.pW v := by rw [pW_apply]; abel
  conv_lhs => rw [hv]
  rw [map_add, map_add, hfix, pW_pU H, zero_add, hwW _ (isW_pW H v)]
end PI.VolSemiDirect.W.PG.Dat
