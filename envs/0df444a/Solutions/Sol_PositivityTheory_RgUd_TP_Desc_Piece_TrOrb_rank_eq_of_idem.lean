-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.rank_eq_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:27.29042+00:00
-- url     : https://prove2.me/submissions/c6f54123-0de1-4674-8225-2822db1be53b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Module
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
variable {k : Type*} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
theorem _root_.solution {R : Type*} [Field R] {P Q : Matrix (Fin N) (Fin N) R} (hP : P * P = P) (hQ : Q * Q = Q)
    (hu : IsUnit (Q * P + (1 - Q) * (1 - P)).det) : P.rank = Q.rank := by
  set u := Q * P + (1 - Q) * (1 - P)
  have h1 : u * P = Q * P := by
    simp only [u, add_mul, mul_assoc, sub_mul, one_mul, hP, sub_self, mul_zero, add_zero]
  have h2 : Q * u = Q * P := by
    simp only [u, mul_add, ← mul_assoc, mul_sub, mul_one, hQ, sub_self, zero_mul, add_zero]
  have : (u * P).rank = (Q * u).rank := by rw [h1, h2]
  rwa [rank_mul_eq_right_of_isUnit_det u P hu, rank_mul_eq_left_of_isUnit_det u Q hu] at this
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
