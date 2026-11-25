-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.TrOrb.isClosed_idem_rank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:14.605404+00:00
-- url     : https://prove2.me/submissions/4d6934fe-408c-43cd-ae7b-1acdba0da7da

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_TrOrbB
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_TrOrb_rank_eq_of_idem

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
theorem _root_.solution (n : ℕ) : IsClosed {P : Matrix (Fin N) (Fin N) k | P * P = P ∧ P.rank = n} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro Q hQ
  by_cases hi : Q * Q = Q
  · have hr : Q.rank ≠ n := fun h => hQ ⟨hi, h⟩
    refine ⟨{P | (Q * P + (1 - Q) * (1 - P)).det ≠ 0}, fun P hP hP' => hr ?_, ?_, ?_⟩
    · rw [← hP'.2]
      exact (rank_eq_of_idem hP'.1 hi (isUnit_iff_ne_zero.2 hP)).symm
    · exact isOpen_ne_fun (((continuous_const.mul continuous_id).add
        (continuous_const.mul (continuous_const.sub continuous_id))).matrix_det) continuous_const
    · show (Q * Q + (1 - Q) * (1 - Q)).det ≠ 0
      have : Q * Q + (1 - Q) * (1 - Q) = 1 := by
        simp only [sub_mul, mul_sub, one_mul, mul_one, hi]; abel
      rw [this, det_one]; exact one_ne_zero
  · exact ⟨{P | P * P ≠ P}, fun P hP hP' => hP hP'.1, isOpen_ne_fun (continuous_id.mul continuous_id) continuous_id,
      hi⟩
end PositivityTheory.RgUd.TP.Desc.Piece.TrOrb
