-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.lam_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:38.415992+00:00
-- url     : https://prove2.me/submissions/df53ee53-f2d3-43fd-9ec6-23b1fc020b18

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
open Classical
attribute [local instance] Ideal.Quotient.field
variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]
namespace PositivityTheory.RgUd.TP.Loc.Ptf
theorem _root_.solution (I : MaximalSpectrum R) : lam (k := k) I 1 ≠ 0 := (exists_lam k I).choose_spec
end PositivityTheory.RgUd.TP.Loc.Ptf
