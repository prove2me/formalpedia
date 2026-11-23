-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.hL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:13:05.779806+00:00
-- url     : https://prove2.me/submissions/3b50db08-7e5b-4d90-84fc-4bd1b4e225db

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ProjGen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
open Formalism.UG
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}
open PI.VolSemiDirect.W.PG.Dat
variable (D : Dat A n r)
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (x y : n → A) : D.hL x y = D.h x y := rfl
end PI.VolSemiDirect.W.PG.Dat
