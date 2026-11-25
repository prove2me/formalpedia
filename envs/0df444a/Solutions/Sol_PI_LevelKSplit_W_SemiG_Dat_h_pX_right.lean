-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.h_pX_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:50:33.813715+00:00
-- url     : https://prove2.me/submissions/0f83fc25-bac4-48e4-a3fd-2cabcb061b5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HermitianIsotropicProjComplement
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_h_pX_left
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
theorem _root_.solution (H : D.Hyp) {y : n → A} (hy : ∀ b, D.h (D.e b) y = 0) (u : n → A) :
    D.h y (D.pX u) = 0 := by
  rw [h_symm H (D.pX u) y, h_pX_left hy, map_zero]
end PI.LevelKSplit.W.SemiG.Dat
