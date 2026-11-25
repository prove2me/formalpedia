-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.comp_iterateFrobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:38.575812+00:00
-- url     : https://prove2.me/submissions/c2338da7-66e2-4d57-bec3-caeb5578ad7a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PSect
open Module Polynomial IntermediateField
variable {E : Type*} [Field E] (p : ℕ) [hp : Fact p.Prime] [CharP E p]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution (j : ℕ) :
    (iterateFrobenius E p j).comp (iterateFrobenius E p 1) = iterateFrobenius E p (j + 1) := by
  ext x
  simp only [RingHom.comp_apply, iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
