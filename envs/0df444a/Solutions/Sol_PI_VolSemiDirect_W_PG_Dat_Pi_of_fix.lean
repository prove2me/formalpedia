-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:21:04.306219+00:00
-- url     : https://prove2.me/submissions/6407c112-c3af-48ef-956b-e6c7c8176e43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_S_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_e_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_h_z_S
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_pU
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
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
    (hf : ∀ a, S (D.f a) = D.f a) (hU : D.Uni S) (v : n → A) : D.Pi S v = S v := by
  have h1 : D.pU (S v) = D.pU v := by
    have a1 : D.pX (S v) = D.pX v := by
      rw [pX_apply, pX_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      conv_lhs => rw [← hf a]
      rw [hU]
    have a2 : D.pXv (S v) = D.pXv v := by
      rw [pXv_apply, pXv_apply]
      simp only [h_e_S hS hU]
    have a3 : D.pz (S v) = D.pz v := by
      rw [pz_apply, pz_apply, h_z_S hS hU]
    rw [pU_apply, a1, a2, a3]; rfl
  have h2 : S (D.pU v) = D.pU v := by
    rw [pU_apply, map_add, map_add, S_pX hS.1, pXv_apply, pz_apply, map_sum, map_smul, hS.2]
    simp only [map_smul, hf]
  have h3 : S (D.pW v) = S v - D.pU v := by rw [pW_apply, map_sub, h2]
  rw [Pi_apply, h3, pW_apply, map_sub, h1, pU_pU H]
  abel
end PI.VolSemiDirect.W.PG.Dat
