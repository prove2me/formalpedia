-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_W_pU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:50:16.016996+00:00
-- url     : https://prove2.me/submissions/3e96dbe1-1bb6-4932-94eb-d373eb354913

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_hermitian_isotropic_proj_complement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_symm


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
theorem _root_.solution (H : D.Hyp) {w : n → A} (hw : IsW D w) (x : n → A) : D.h w (D.pU x) = 0 := by
  rw [h_symm H (D.pU x) w, hermitian_isotropic_proj_complement H hw, map_zero]
end PI.LevelKSplit.W.SemiG.Dat
