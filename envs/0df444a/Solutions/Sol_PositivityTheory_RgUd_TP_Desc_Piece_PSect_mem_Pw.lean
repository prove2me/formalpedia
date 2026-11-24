-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.mem_Pw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:52.355143+00:00
-- url     : https://prove2.me/submissions/8f02c802-5a7d-434a-8d54-9d5f377f3d60

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_MemPw

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
open Module
variable {k : Type*} [Field k]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution {B : Type*} [CommRing B] [Algebra k B] (p c : ℕ) [Fact p.Prime] [CharP k p]
    (hroot : ∀ a : k, ∃ w : B, w ^ (p ^ c) = algebraMap k B a) {b : B} :
    b ∈ Pw k B (p ^ c) ↔ ∃ w : B, w ^ (p ^ c) = b := by
  unfold Pw
  constructor
  · intro hb
    rcases subsingleton_or_nontrivial B with hB | hB
    · exact ⟨b, Subsingleton.elim _ _⟩
    have : CharP B p := charP_of_injective_algebraMap' k p
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    | algebraMap r => exact hroot r
    | add x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ + w₂, add_pow_char_pow w₁ w₂ p c⟩
    | mul x y _ _ hx hy =>
      obtain ⟨w₁, rfl⟩ := hx
      obtain ⟨w₂, rfl⟩ := hy
      exact ⟨w₁ * w₂, mul_pow w₁ w₂ _⟩
  · rintro ⟨w, rfl⟩
    exact Algebra.subset_adjoin ⟨w, rfl⟩
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
