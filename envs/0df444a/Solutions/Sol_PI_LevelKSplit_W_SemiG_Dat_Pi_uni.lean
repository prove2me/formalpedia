-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.Pi_uni
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:06:10.694174+00:00
-- url     : https://prove2.me/submissions/31158265-4ef9-40dc-9e25-9b7988e5dbc0

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_e_pX
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_pX_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_pX_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_complement_proj_image
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_dec
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_smul_right
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
section
noncomputable section
namespace PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace Dat
variable {D : Dat A n r}
private theorem D_h_sub_left (a b c : n → A) : D.h (a - b) c = D.h a c - D.h b c := by
  rw [sub_eq_add_neg, ← neg_one_smul A b, h_add_left, h_smul_left, map_neg, map_one, neg_one_mul,
    ← sub_eq_add_neg]
private theorem D_h_sub_right (a b c : n → A) : D.h c (a - b) = D.h c a - D.h c b := by
  rw [sub_eq_add_neg, ← neg_one_smul A b, h_add_right, h_smul_right, neg_one_mul, ← sub_eq_add_neg]
end Dat
end PI.LevelKSplit.W.SemiG
end
end

set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.SemiG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.LevelKSplit.W.SemiG.Dat
variable {D : Dat A n r}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (H : D.Hyp) {S : (n → A) →ₗ[A] (n → A)} (hW : D.MapW S) (hU : D.Uni S) :
    D.Uni (D.Pi S) := by
  intro x y
  have key : ∀ w w', IsW D w → IsW D w' → D.h (D.pW (S w)) (D.pW (S w')) = D.h w w' := by
    intro w w' hw hw'
    rw [complement_proj_image hW hw, complement_proj_image hW hw', D_h_sub_left, D_h_sub_right, D_h_sub_right,
      h_pX_left (hW w' hw').1, h_pX_right H (hW w hw).1, h_pX_left (fun b => h_e_pX H b (S w')), hU]
    simp
  have hPU : ∀ v, D.pU (D.Pi S v) = D.pU v := fun v => by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pU_pU H, pU_pW H, add_zero]
  have hPW : ∀ v, D.pW (D.Pi S v) = D.pW (S (D.pW v)) := fun v => by
    simp only [Pi, LinearMap.add_apply, LinearMap.comp_apply, map_add, pW_pU H, pW_pW H, zero_add]
  rw [h_dec H, hPU, hPU, hPW, hPW, key _ _ (isW_pW H x) (isW_pW H y), ← h_dec H]
end PI.LevelKSplit.W.SemiG.Dat
