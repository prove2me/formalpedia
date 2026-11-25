-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pW_of_isW
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:12.974079+00:00
-- url     : https://prove2.me/submissions/8b01fcb1-ae10-4043-b820-760ac1822770

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_of_isW

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
variable (D : Dat A n r)
variable {D}
variable (D)
variable {D}
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution {w : n → A} (hw : IsW D w) : D.pW w = w := by
  rw [pW_apply, pU_of_isW hw, sub_zero]
end PI.LevelKSplit.W.SemiG.Dat
