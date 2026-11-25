-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Loc.Ptf.eI_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:30.382235+00:00
-- url     : https://prove2.me/submissions/0c7d357a-fe6a-4383-83e4-ce1d42fa7f00

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
theorem _root_.solution {I J : MaximalSpectrum R} (h : J ≠ I) : eI I ∈ J.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne h]
end PositivityTheory.RgUd.TP.Loc.Ptf
