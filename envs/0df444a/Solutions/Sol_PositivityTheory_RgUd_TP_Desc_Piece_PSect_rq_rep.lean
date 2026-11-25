-- Prove2me | solution 1 for PositivityTheory.RgUd.TP.Desc.Piece.PSect.rq_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:55:42.669426+00:00
-- url     : https://prove2.me/submissions/e0a2bc09-b760-4757-8f7c-f6ddb52de9c5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_UnitaryDualProof_TwistedPieces_FiniteDimensionalDescent_ClosedOrbitPieces_FrobeniusSections_RqLift

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
variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect
theorem _root_.solution (χ : k[X]) (hχ : χ.Monic) (q d : ℕ) (hd : χ.natDegree ≤ d) (r : Rq A χ q) :
    ∃ a : Fin d → A, r = Ideal.Quotient.mk _ (∑ l : Fin d, C (a l) * X ^ (l : ℕ)) := by
  classical
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective r
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, by congr 1; exact Subsingleton.elim _ _⟩
  have hmon : (χ.map (algebraMap k A)).Monic := hχ.map _
  have hmem : P - P %ₘ χ.map (algebraMap k A) ∈ Iq A χ q := by
    have e : P - P %ₘ χ.map (algebraMap k A) = χ.map (algebraMap k A) * (P /ₘ χ.map (algebraMap k A)) := by
      have h := modByMonic_add_div P (χ.map (algebraMap k A))
      linear_combination -h
    rw [e]
    exact Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
  have hdeg : (P %ₘ χ.map (algebraMap k A)).degree < d :=
    calc (P %ₘ χ.map (algebraMap k A)).degree < (χ.map (algebraMap k A)).degree := degree_modByMonic_lt _ hmon
      _ ≤ (χ.map (algebraMap k A)).natDegree := degree_le_natDegree
      _ ≤ d := by exact_mod_cast natDegree_map_le.trans hd
  refine ⟨fun l => (P %ₘ χ.map (algebraMap k A)).coeff l, ?_⟩
  rw [Ideal.Quotient.eq.mpr hmem]
  congr 1
  rw [show (∑ l : Fin d, C ((P %ₘ χ.map (algebraMap k A)).coeff (l : ℕ)) * X ^ (l : ℕ)) =
      ∑ i ∈ Finset.range d, C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i from
    (Finset.sum_range (fun i => C ((P %ₘ χ.map (algebraMap k A)).coeff i) * X ^ i)).symm]
  by_cases h0 : P %ₘ χ.map (algebraMap k A) = 0
  · rw [h0]
    simp
  · have h := as_sum_range' _ d ((natDegree_lt_iff_degree_lt h0).mpr hdeg)
    simp only [← C_mul_X_pow_eq_monomial] at h
    exact h
end PositivityTheory.RgUd.TP.Desc.Piece.PSect
