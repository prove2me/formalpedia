-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.sq_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:52.236926+00:00
-- url     : https://prove2.me/submissions/6de8f0e5-e499-4c76-949f-e535941aeda6

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_SqSumLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
