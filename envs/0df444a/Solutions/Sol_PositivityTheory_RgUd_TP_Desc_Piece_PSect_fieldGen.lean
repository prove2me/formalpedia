-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fieldGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:28:54.120376+00:00
-- url     : https://prove2.me/submissions/4969a21a-54e2-4fb9-9c15-6e57325b6f0e

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FieldGen
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_deg
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_Pj_zero
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_frob
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pj


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
open Module Polynomial
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {k E : Type*} [Field k] [Field E] [Algebra k E] [FiniteDimensional k E]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hroot : ∀ a : k, ∃ w : E, w ^ (p ^ c) = algebraMap k E a) :
    ∃ n : ℕ, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Algebra.adjoin k (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
  have : CharP E p := charP_of_injective_algebraMap (algebraMap k E).injective p
  have hdeg := fl_deg p c hroot
  suffices H : ∃ n, finrank k (Tw k p c) = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ by
    obtain ⟨n, hn, α, hα⟩ := H
    refine ⟨n, hn, α, ?_⟩
    have hadj : IntermediateField.adjoin k
        (Set.range (fun b : E => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
      apply IntermediateField.toSubfield_injective
      rw [IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield, eq_top_iff, ← hα]
      apply Subfield.closure_mono
      apply Set.union_subset
      · intro y hy
        exact Or.inr (Or.inl ((mem_Pj p).1 hy))
      · intro y hy
        exact Or.inr (Or.inr hy)
    rw [← IntermediateField.adjoin_toSubalgebra, hadj, IntermediateField.top_toSubalgebra]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨0, ?_, Fin.elim0, ?_⟩
    · rw [← hdeg, pow_zero, Subfield.relfinrank_eq_one_iff, Pj_zero]
    · rw [Pj_zero]
      exact eq_top_iff.2 fun y _ => Subfield.subset_closure (Or.inl (Subfield.mem_top y))
  · have hfin : (Pj E p c).relfinrank ⊤ ≠ 0 := by
      rw [hdeg]
      exact Module.finrank_pos.ne'
    obtain ⟨n, hn, α, hα⟩ := fl_frob p c hc hfin
    exact ⟨n, hdeg ▸ hn, α, hα⟩
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
