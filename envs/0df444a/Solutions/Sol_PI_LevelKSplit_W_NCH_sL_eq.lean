-- Prove2me | solution 1 for PI.LevelKSplit.W.NCH.sL_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:02:05.072942+00:00
-- url     : https://prove2.me/submissions/2f133347-481c-4c3d-bde8-c7bc4ecee4e3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ReflectionFixesNormal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCH
open PI.VolSemiDirect.W.PG PI.VolSemiDirect.W.PG.Dat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace PI.LevelKSplit.W.NCH
theorem _root_.solution (D : Dat A n r) (half : A) (y : Fin r → n → A) (v : n → A) :
    sL D half y v = v + tV D half y v := by
  simp only [sL_apply, tV, add_sub_assoc]
end PI.LevelKSplit.W.NCH
