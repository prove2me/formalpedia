-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pW_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:10.830916+00:00
-- url     : https://prove2.me/submissions/c6435f2d-6104-473b-9f3f-ce0355351a91

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_SemiGen

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
namespace PI.LevelKSplit.W.SemiG.Dat
theorem _root_.solution (v : n → A) : D.pW v = v - D.pU v := rfl
end PI.LevelKSplit.W.SemiG.Dat
