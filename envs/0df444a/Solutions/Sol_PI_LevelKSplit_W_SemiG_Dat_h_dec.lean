-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_dec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:58:03.734143+00:00
-- url     : https://prove2.me/submissions/ad4d6ddb-4abf-4f40-8f94-a2953c9cb9ca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hermitian_isotropic_proj_complement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_W_pU
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_left
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_add_right
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_isW_pW


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
theorem _root_.solution (H : D.Hyp) (x y : n → A) :
    D.h x y = D.h (D.pU x) (D.pU y) + D.h (D.pW x) (D.pW y) := by
  have ex : x = D.pU x + D.pW x := by simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]; abel
  have ey : y = D.pU y + D.pW y := by simp only [pW, LinearMap.sub_apply, LinearMap.id_apply]; abel
  conv_lhs => rw [ex, ey]
  rw [h_add_left, h_add_right, h_add_right, hermitian_isotropic_proj_complement H (isW_pW H y), h_W_pU H (isW_pW H x)]
  simp
end PI.LevelKSplit.W.SemiG.Dat
