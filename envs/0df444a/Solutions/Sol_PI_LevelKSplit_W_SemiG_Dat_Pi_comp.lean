-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:11:02.86229+00:00
-- url     : https://prove2.me/submissions/af5663e3-0957-4d06-a89e-915d21e48e89

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_S_pX
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_complement_proj_image
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isW_pW
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_pW
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_pW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) {S S' : (n → A) →ₗ[A] (n → A)} (hX : D.MapX S) (hW' : D.MapW S')
    (v : n → A) : D.Pi S (D.Pi S' v) = D.Pi (S ∘ₗ S') v := by
  have hw := isW_pW H v
  simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pU_pU H, pU_pW H, pW_pU H, pW_pW H,
    map_zero, add_zero, zero_add]
  rw [complement_proj_image hW' hw, map_sub, map_sub, pW_S_pX H hX, sub_zero]
end PI.LevelKSplit.W.SemiG.Dat
