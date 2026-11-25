-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_greedy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:59.975675+00:00
-- url     : https://prove2.me/submissions/9251e62d-f763-446f-b327-8b6452701c59

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_step

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
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (p : ℕ) [hp : Fact p.Prime] [CharP E p] (h : ∀ x : E, x ^ p ∈ Set.range (algebraMap F E)) :
    ∀ (N : ℕ) (L : IntermediateField F E), L.relfinrank ⊤ = N →
      ∃ n, L.relfinrank ⊤ = p ^ n ∧ ∃ α : Fin n → E, L ⊔ adjoin F (Set.range α) = ⊤ := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro L hL
  by_cases hT : L = ⊤
  · subst hT
    exact ⟨0, by simp [relfinrank_self], Fin.elim0, top_sup_eq _⟩
  obtain ⟨x, -, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.2 hT)
  set L' : IntermediateField F E := (adjoin L ({x} : Set E)).restrictScalars F with hL'
  have hsup : L' = L ⊔ adjoin F ({x} : Set E) := by rw [hL', restrictScalars_adjoin_eq_sup]
  have hle : L ≤ L' := hsup ▸ le_sup_left
  have hdeg : L.relfinrank L' = p := by
    rw [relfinrank_eq_finrank_of_le hle]
    have : extendScalars hle = adjoin L ({x} : Set E) :=
      restrictScalars_injective F (by rw [extendScalars_restrictScalars])
    rw [this, fl_step p h L hx]
  have hmul := relfinrank_mul_relfinrank hle (le_top : L' ≤ ⊤)
  have hpos : 0 < L.relfinrank ⊤ := by
    rw [relfinrank_top_right]; exact Module.finrank_pos
  have hlt : L'.relfinrank ⊤ < N := by
    rw [← hL, ← hmul, hdeg]
    have h2 := hp.out.two_le
    have : 0 < L'.relfinrank ⊤ := by
      rcases Nat.eq_zero_or_pos (L'.relfinrank ⊤) with h0 | h0
      · rw [← hmul, h0, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
      · exact h0
    nlinarith
  obtain ⟨m, hm, β, hβ⟩ := ih _ hlt L' rfl
  refine ⟨m + 1, ?_, Fin.cons x β, ?_⟩
  · rw [← hmul, hdeg, hm, pow_succ']
  · rw [Fin.range_cons, Set.insert_eq, adjoin_union, ← sup_assoc, ← hsup, hβ]
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
