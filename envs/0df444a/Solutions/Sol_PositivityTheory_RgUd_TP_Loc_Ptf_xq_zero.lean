-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.xq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:54:56.533388+00:00
-- url     : https://prove2.me/submissions/89449b18-5edf-4157-b9cb-8915e8e25d83

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
theorem _root_.solution (I : Ideal R) : xq I (0 : V →ₗ[R] V) = 0 := xq_ext I fun _ => rfl
end PositivityTheory.RgUd.TP.Loc.Ptf
