-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.closure_Pj_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:34.508025+00:00
-- url     : https://prove2.me/submissions/fd78c6b8-f109-4825-b230-3405d8dae143

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pj
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_Pj_zero
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_map_top_Pj

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
theorem _root_.solution {S : Set E} (hS : Subfield.closure ((Pj E p 1 : Set E) ∪ S) = ⊤)
    (j : ℕ) : Subfield.closure ((Pj E p j : Set E) ∪ S) = ⊤ := by
  have key : ∀ i, Pj E p i ≤ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S) := by
    intro i
    rw [← map_top_Pj p i, ← hS, Subfield.map_le_iff_le_comap, Subfield.closure_le]
    rintro y (hy | hy)
    · change y ∈ Pj E p 1 at hy
      obtain ⟨x, rfl⟩ := (mem_Pj p).1 hy
      rw [SetLike.mem_coe, Subfield.mem_comap]
      apply Subfield.subset_closure
      left
      exact (mem_Pj p).2 ⟨x, by rw [iterateFrobenius_def, ← pow_mul, ← pow_add, add_comm]⟩
    · rw [SetLike.mem_coe, Subfield.mem_comap, iterateFrobenius_def]
      exact pow_mem (Subfield.subset_closure (Set.mem_union_right _ hy) :
        y ∈ Subfield.closure ((Pj E p (i + 1) : Set E) ∪ S)) _
  induction j with
  | zero =>
    rw [Pj_zero]
    exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  | succ j ih =>
    refine eq_top_iff.2 (ih ▸ Subfield.closure_le.2 (Set.union_subset (key j) ?_))
    exact fun y hy => Subfield.subset_closure (Or.inr hy)
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
