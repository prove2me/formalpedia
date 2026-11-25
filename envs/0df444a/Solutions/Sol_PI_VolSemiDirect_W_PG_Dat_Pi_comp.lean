-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:02.821828+00:00
-- url     : https://prove2.me/submissions/e2e9c772-cba2-4d3d-8c8f-265cc31ad5b2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_S_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_complement_proj_image
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_of_isW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pX


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
theorem _root_.solution (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hS : ∀ a, S (D.e a) = D.e a)
    (hS' : D.FixEZ S') (hU' : D.Uni S') (v : n → A) :
    D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by
  have h1 : D.pU (D.Pi S' v) = D.pU v := by
    rw [Pi_apply, map_add, pU_pU H, pU_of_isW (isW_pW H _), add_zero]
  have h2 : D.pW (D.Pi S' v) = D.pW (S' (D.pW v)) := by
    rw [Pi_apply, map_add, pW_pU H, pW_pW H, zero_add]
  rw [Pi_apply D S, h1, h2, complement_proj_image hS' hU' (isW_pW H v), map_sub, S_pX hS, map_sub, pW_pX H,
    sub_zero, Pi_apply]
  rfl
end PI.VolSemiDirect.W.PG.Dat
