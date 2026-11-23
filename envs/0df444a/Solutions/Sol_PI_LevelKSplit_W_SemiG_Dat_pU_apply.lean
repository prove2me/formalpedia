-- Prove2me | solution 1 for PI.LevelKSplit.W.SemiG.Dat.pU_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:28.402419+00:00
-- url     : https://prove2.me/submissions/7d03644e-4a22-4edc-9c07-a89c08740b53

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
theorem _root_.solution (v : n → A) : D.pU v = D.pX v + D.pXv v + D.pz v := rfl
end PI.LevelKSplit.W.SemiG.Dat
