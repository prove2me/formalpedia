-- Prove2me | solution 1 for PositivityTheory.ThKG.Loc.Cone.Vf.Adj.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:11.116186+00:00
-- url     : https://prove2.me/submissions/ca2b3de1-ef35-480e-94f7-2321775e5aa7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKG PositivityTheory.ThKG.Loc PositivityTheory.ThKG.Loc.Cone PositivityTheory.ThKG.Loc.Cone.Vf
open Matrix GlobalTheory.WeilM
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) [Fintype β] [DecidableEq β]
variable {c} {J : Matrix β β A}
namespace PositivityTheory.ThKG.Loc.Cone.Vf
namespace Adj
theorem _root_.solution : Adj c J 1 1 := by simp [Adj, mapc_one]
end Adj
end PositivityTheory.ThKG.Loc.Cone.Vf
