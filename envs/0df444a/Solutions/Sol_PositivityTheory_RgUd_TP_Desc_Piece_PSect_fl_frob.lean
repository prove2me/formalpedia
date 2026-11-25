-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.fl_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:22:04.178492+00:00
-- url     : https://prove2.me/submissions/083761ab-4f1f-4243-a710-353c66594791

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_CompIterateFrobenius
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_fl_main
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_mem_Pj
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_relfinrank_Pj
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_closure_Pj_eq_top

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
theorem _root_.solution (c : ℕ) (hc : 0 < c) (hfin : (Pj E p c).relfinrank ⊤ ≠ 0) :
    ∃ n, (Pj E p c).relfinrank ⊤ = (p ^ c) ^ n ∧
      ∃ α : Fin n → E, Subfield.closure ((Pj E p c : Set E) ∪ Set.range α) = ⊤ := by
  have h1 : (Pj E p 1).relfinrank ⊤ ≠ 0 := by
    intro h0
    apply hfin
    rw [relfinrank_Pj, h0, zero_pow hc.ne']
  haveI : FiniteDimensional (Pj E p 1) E :=
    Module.finite_of_finrank_pos (by rw [← Subfield.relfinrank_top_right]; exact Nat.pos_of_ne_zero h1)
  obtain ⟨n, hn, α, hα⟩ := fl_main (F := Pj E p 1) (E := E) p
    (fun x => ⟨⟨x ^ p, (mem_Pj p).2 ⟨x, by rw [pow_one]⟩⟩, rfl⟩)
  refine ⟨n, ?_, α, closure_Pj_eq_top p ?_ c⟩
  · rw [relfinrank_Pj, Subfield.relfinrank_top_right, hn, ← pow_mul, ← pow_mul, mul_comm]
  · have := congrArg IntermediateField.toSubfield hα
    rw [adjoin_toSubfield, top_toSubfield] at this
    have hr : Set.range (algebraMap (Pj E p 1) E) = (Pj E p 1 : Set E) := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact z.2
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rwa [hr] at this
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
