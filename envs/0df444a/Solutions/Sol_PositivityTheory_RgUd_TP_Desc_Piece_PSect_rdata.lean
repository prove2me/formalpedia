-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.rdata
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:45:14.794112+00:00
-- url     : https://prove2.me/submissions/d877f2c7-8a07-4852-9708-378ccb858f75

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_FinrankAdjoinPowLe
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_SEps
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_Rdata
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_idem
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_sEps
import Theorems.Thm_PositivityTheory_RgUd_TP_Desc_Piece_PSect_sectionEx


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
theorem _root_.solution {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R] [IsPrincipalIdealRing R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ (r : ℕ) (s : Fin r → R) (c' : Fin r → Fin r → Fin r → k) (u : Fin r → k) (ε : R) (m : ℕ)
      (κ : Fin m → Fin r → k),
      (∀ j j', s j * s j' = ∑ t, c' j j' t • s t) ∧ ∑ j, u j • s j = 1 ∧ ε ^ (p ^ c) = 0 ∧
      (∀ y : R, ∃ γ : Fin (p ^ c) → Fin r → k, y = ∑ l, ∑ j, γ l j • (s j * ε ^ (l : ℕ))) ∧
      (∀ t, IsIdempotentElem (∑ j, κ t j • s j)) ∧ (∑ t, ∑ j, κ t j • s j) = 1 ∧
      (∀ t t', t ≠ t' → (∑ j, κ t j • s j) * (∑ j, κ t' j • s j) = 0) ∧
      ∀ t (v : Fin r → k), (∑ j, v j • s j) * (∑ j, κ t j • s j) = 0 ∨
        ∃ w : R, (∑ j, v j • s j) * (∑ j, κ t j • s j) * w = ∑ j, κ t j • s j := by
  classical
  obtain ⟨S, hSred, hSlift⟩ := sectionEx p c hnil hroot
  have : IsReduced S := ⟨fun x hx => Subtype.ext (hSred x x.2 (hx.map S.val))⟩
  have : FiniteDimensional k S := FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
  obtain ⟨m, e, he1, he2, he3, he4⟩ := idem (k := k) (S := S)
  obtain ⟨ε, hεn, hε⟩ := sEps S hSlift (p ^ c) hnil
  let b := Module.finBasis k S
  have hsum : ∀ x : S, ∑ j, b.repr x j • ((b j : S) : R) = (x : R) := by
    intro x
    have h := congrArg S.val (b.sum_repr x)
    rw [map_sum] at h
    simpa using h
  refine ⟨finrank k S, fun j => (b j : R), fun j j' t => b.repr (b j * b j') t, fun j => b.repr 1 j, ε, m,
    fun t j => b.repr (e t) j, ?_, ?_, hnil ε hεn, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j'
    rw [hsum]; rfl
  · rw [hsum]; rfl
  · intro y
    obtain ⟨σ, hσ, hy⟩ := hε y
    refine ⟨fun l j => b.repr ⟨σ l, hσ l⟩ j, ?_⟩
    rw [hy]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [← smul_mul_assoc, ← Finset.sum_mul]
    rw [hsum]
  · intro t
    simp only [hsum]
    exact congrArg Subtype.val (he1 t)
  · simp only [hsum]
    have h := congrArg S.val he2
    rw [map_sum, map_one] at h
    simpa using h
  · intro t t' htt
    simp only [hsum]
    exact congrArg Subtype.val (he3 t t' htt)
  · intro t v
    simp only [hsum]
    have hx : ∑ j, v j • ((b j : S) : R) = ((∑ j, v j • b j : S) : R) := by
      simp
    rw [hx]
    rcases he4 t (∑ j, v j • b j) with h0 | ⟨w, hw⟩
    · left; exact congrArg Subtype.val h0
    · right; exact ⟨w, congrArg Subtype.val hw⟩
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
