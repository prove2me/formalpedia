-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_N_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:20:46.515235+00:00
-- url     : https://prove2.me/submissions/54660da4-07ba-48ca-9eb9-cb74b388ab02

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_HermitianIsotropicProjComplement
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_S_pX
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_complement_proj_image
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_mem_span
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_Pi_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_isW_pW
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pU_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pW_apply
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
theorem _root_.solution (H : D.Hyp) {S Si : (n → A) →ₗ[A] (n → A)} (hS : D.FixEZ S)
    (hSi : D.FixEZ Si) (hUi : D.Uni Si) (hSSi : ∀ v, S (Si v) = v) (v : n → A)
    (hv : ∀ a, D.h (D.e a) v = 0) :
    S (D.Pi Si v) - v ∈ Submodule.span A (Set.range D.e) := by
  have hw := isW_pW H v
  have hpU : S (D.pU v) = D.pU v := by
    rw [pU_apply, map_add, map_add, S_pX hS.1, pXv_apply, pz_apply, map_smul, hS.2]
    simp [hv]
  have key : S (D.Pi Si v) - v = -D.pX (Si (D.pW v)) := by
    rw [Pi_apply, complement_proj_image hSi hUi hw, map_add, map_sub, hSSi, S_pX hS.1, hpU, pW_apply]
    abel
  rw [key]
  exact Submodule.neg_mem _ (pX_mem_span _)
end PI.VolSemiDirect.W.PG.Dat
