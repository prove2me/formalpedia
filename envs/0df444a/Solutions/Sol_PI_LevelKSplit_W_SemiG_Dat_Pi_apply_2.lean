-- Prove2me | solution 2 for PI.LevelKSplit.W.SemiG.Dat.Pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:18:44.465801+00:00
-- url     : https://prove2.me/submissions/4e0378e8-9252-4415-abde-69d8fe6a20c9

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
theorem _root_.solution (S : (n → A) →ₗ[A] (n → A)) (v : n → A) :
    D.Pi S v = D.pU v + D.pW (S (D.pW v)) := rfl
end PI.LevelKSplit.W.SemiG.Dat
