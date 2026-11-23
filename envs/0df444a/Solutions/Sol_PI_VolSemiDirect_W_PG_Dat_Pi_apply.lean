-- Prove2me | solution 1 for PI.VolSemiDirect.W.PG.Dat.Pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:52.320319+00:00
-- url     : https://prove2.me/submissions/bdf4e98f-d1da-4331-bf95-acc8cb933930

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
variable {D}
variable (D)
namespace PI.VolSemiDirect.W.PG.Dat
theorem _root_.solution (S : (n → A) →ₗ[A] (n → A)) (v : n → A) :
    D.Pi S v = D.pU v + D.pW (S (D.pW v)) := rfl
end PI.VolSemiDirect.W.PG.Dat
