-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PDich.rank_sum_orth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:15.246855+00:00
-- url     : https://prove2.me/submissions/a1632298-e799-41fa-b9c2-a623742e1d68

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_RankPosOfNe
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_rank_add_orth
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PDich_idem_sum_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.RgUd PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc PositivityTheory.RgUd.TP.Desc.Piece PositivityTheory.RgUd.TP.Desc.Piece.PDich
open Matrix
variable {k : Type} [Field k] {N : ℕ}
namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich
theorem _root_.solution {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hid' : ∀ j ∈ s, IsIdempotentElem (e j) := fun j hj => hid j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → e j * e l = 0 := fun j hj l hl h =>
      ho j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) h
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hid' ho']
    refine rank_add_orth (hid i (Finset.mem_insert_self i s)) (idem_sum_orth s e hid' ho') ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => ho j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (fun h => hi (h ▸ hj))
end PositivityTheory.RgUd.TP.Desc.Piece.PDich
