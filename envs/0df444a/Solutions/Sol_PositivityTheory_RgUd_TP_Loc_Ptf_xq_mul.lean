-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.xq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:12.264827+00:00
-- url     : https://prove2.me/submissions/4091a98e-c4bf-4327-a18e-febfa927318b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_LocalTraceForms_TraceCompSmulRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Loc PositivityTheory.RgUd.TP.Loc.Ptf
variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x * y) = xq I x * xq I y :=
  xq_ext I fun _ => rfl
end PositivityTheory.RgUd.TP.Loc.Ptf
