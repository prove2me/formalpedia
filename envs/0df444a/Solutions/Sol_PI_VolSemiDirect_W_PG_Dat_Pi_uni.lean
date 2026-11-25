-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:14:40.174395+00:00
-- url     : https://prove2.me/submissions/847a30c2-de18-4201-af74-73e4784d8db0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_pX_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_complement_proj_image
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_dec
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sub_left
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_sub_right
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_of_isW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_pW


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
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S) (hU : D.Uni S) :
    D.Uni (D.Pi S) := by
  intro x y
  have hW : ∀ w w' : n → A, IsW D w → IsW D w' →
      D.h (D.pW (S w)) (D.pW (S w')) = D.h w w' := by
    intro w w' hw hw'
    have he : ∀ {u : n → A}, IsW D u → ∀ b, D.h (D.e b) (S u) = 0 := fun hu b => by
      rw [h_e_S hS hU, hu.1 b]
    rw [complement_proj_image hS hU hw, complement_proj_image hS hU hw', h_sub_left, h_sub_right, h_sub_right,
      h_pX_left (he hw'), h_pX_left (fun b => h_e_pX H b _), h_pX_right H (he hw), hU]
    ring
  have hp : ∀ v, D.pU (D.Pi S v) = D.pU v := fun v => by
    rw [Pi_apply, map_add, pU_pU H, pU_of_isW (isW_pW H _), add_zero]
  have hq : ∀ v, D.pW (D.Pi S v) = D.pW (S (D.pW v)) := fun v => by
    rw [Pi_apply, map_add, pW_pU H, pW_pW H, zero_add]
  rw [h_dec H (D.Pi S x), hp, hp, hq, hq, hW _ _ (isW_pW H x) (isW_pW H y), ← h_dec H]
end PI.VolSemiDirect.W.PG.Dat
