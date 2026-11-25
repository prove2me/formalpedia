-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pW_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:51:06.052619+00:00
-- url     : https://prove2.me/submissions/c085987d-9821-4179-bed9-7eea04721c63

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pW_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pU_f

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
theorem _root_.solution (H : D.Hyp) (b : Fin r) : D.pW (D.f b) = 0 := by
  rw [pW_apply, pU_f H, sub_self]
end PI.LevelKSplit.W.SemiG.Dat
