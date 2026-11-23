-- Prove2me | solution 1 for PI.LevelKSplit.W.NCL.decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:31:35.840499+00:00
-- url     : https://prove2.me/submissions/9f0d0092-2e4f-49e3-82ae-39ad756be434

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ModVec
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_LevLSubPerp
import Theorems.Thm_PI_LevelKSplit_W_NCL_pV_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.LevelKSplit PI.LevelKSplit.W PI.LevelKSplit.W.NCL
open PI.VolSemiDirect.W.PG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
namespace PI.LevelKSplit.W.NCL
theorem _root_.solution (D : Dat A n r) (x : n → A) : x = pV D x + D.pX x + D.pXv x := by
  rw [pV_apply]
  abel
end PI.LevelKSplit.W.NCL
