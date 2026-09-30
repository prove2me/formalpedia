-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_fibre_anchor_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-22T16:22:18.417297+00:00
-- url     : https://prove2.me/submissions/191492cf-c37a-4037-a078-b2a81b96208b

import Definitions.Def_WeierstrassEllipticZeta_FibreEnumeratedAnchors
import Theorems.Thm_WeierstrassEllipticZeta_finite_elementary_locus_vanishing
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Topology.DiscreteSubset
import Mathlib.Tactic

noncomputable section
open scoped Classical Topology
namespace WeierstrassEllipticZeta

private def locusValue (S : Fin 5 → ℂ → ℂ) (Q : MvPolynomial (Fin 7) ℂ)
    (w : Fin 3 → ℂ) : ℂ :=
  MvPolynomial.eval ![1, w 0, S 0 (w 1), S 1 (w 1), S 2 (w 1),
    S 3 (w 1) + w 2 * S 0 (w 1), S 4 (w 1) + w 2 * S 2 (w 1)] Q

private lemma fibre_values_of_samples (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n) (r : Fin 3 → ℂ)
    (hz : ∀ w ∈ elementaryLocusSamples .fibre r m n, locusValue S Q w = 0) :
    ∀ t u : ℂ, locusValue S Q ![t, r 1, u] = 0 := by
  have hall := ((finite_elementary_locus_vanishing S Q m n hQ .fibre r).2.2).mpr hz
  intro t u
  have hv := hall (r + ![t - r 0, 0, u - r 2])
    ⟨![t - r 0, 0, u - r 2], by simp [elementaryDirections], rfl⟩
  simpa [locusValue] using hv


private lemma nonzero_integer_slice (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0) :
    ∃ (i : Fin (m + 1)) (j : Fin (n + 1)),
      (fun b : ℂ => locusValue S Q ![(i.val : ℂ), b, (j.val : ℂ)]) ≠ 0 := by
  by_contra! hz
  apply hne
  funext z
  have hsamples : ∀ w ∈ elementaryLocusSamples .fibre ![0, z, 0] m n,
      locusValue S Q w = 0 := by
    rintro w hw
    obtain ⟨ij, hij, rfl⟩ := Finset.mem_image.mp hw
    have hi := Finset.mem_range.mp (Finset.mem_product.mp hij).1
    have hj := Finset.mem_range.mp (Finset.mem_product.mp hij).2
    have he := congrFun (hz ⟨ij.1, hi⟩ ⟨ij.2, hj⟩) z
    simpa [locusValue] using he
  have hv := fibre_values_of_samples S Q m n hQ ![0, z, 0] hsamples z 0
  simpa [locusValue] using hv

private lemma slice_analytic (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) (t u : ℂ) :
    AnalyticOnNhd ℂ (fun b : ℂ => locusValue S Q ![t, b, u]) Set.univ := by
  intro b _
  change AnalyticAt ℂ (fun b : ℂ => MvPolynomial.eval
    ![1, t, S 0 b, S 1 b, S 2 b, S 3 b + u * S 0 b, S 4 b + u * S 2 b] Q) b
  apply AnalyticAt.aeval_mvPolynomial
  intro j
  fin_cases j
  · exact analyticAt_const
  · exact analyticAt_const
  · exact hS 0 b (Set.mem_univ b)
  · exact hS 1 b (Set.mem_univ b)
  · exact hS 2 b (Set.mem_univ b)
  · exact (hS 3 b (Set.mem_univ b)).add
      (analyticAt_const.mul (hS 0 b (Set.mem_univ b)))
  · exact (hS 4 b (Set.mem_univ b)).add
      (analyticAt_const.mul (hS 2 b (Set.mem_univ b)))

private lemma finite_compact_zeros (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hne : f ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) : {b | b ∈ K ∧ f b = 0}.Finite := by
  have hc : ∀ᶠ b in Filter.codiscreteWithin (Set.univ : Set ℂ), f b ≠ 0 :=
    (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ).resolve_left
      (by intro hz; exact hne (funext fun b => hz (Set.mem_univ b)))
  have hk := hK.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono (Set.subset_univ K)) hc)
  apply hk.subset
  intro b hb
  exact ⟨hb.1, fun hn => hn hb.2⟩

private lemma fibre_coordinates_finite (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) :
    {b | b ∈ K ∧ () ∈ fibreAnchorChoices S Q m n b}.Finite := by
  obtain ⟨i, j, hij⟩ := nonzero_integer_slice S Q m n hQ hne
  apply (finite_compact_zeros _ (slice_analytic S hS Q i.val j.val) hij K hK).subset
  intro b hb
  refine ⟨hb.1, ?_⟩
  have hv := fibre_values_of_samples S Q m n hQ ![0, b, 0]
    (Finset.mem_filter.mp hb.2).2 i.val j.val
  exact hv


end WeierstrassEllipticZeta
open WeierstrassEllipticZeta

theorem solution
    (Λ : Submodule ℤ ℂ) (η : Λ →ₗ[ℤ] ℂ) (X : Finset ℂ)
    (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (Q : MvPolynomial (Fin 7) ℂ) (m n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 0 + d 1 = m ∧
      d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (hne : (fun z : ℂ => MvPolynomial.eval
      ![1, z, S 0 z, S 1 z, S 2 z, S 3 z, S 4 z] Q) ≠ 0)
    (K : Set ℂ) (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K) :
    (∃ Z : Finset ℂ, ∀ b : ℂ,
      b ∈ Z ↔ b ∈ K ∧ () ∈ fibreAnchorChoices S Q m n b) ∧
    ∀ Z : Finset ℂ,
      (∀ b : ℂ, b ∈ Z ↔ b ∈ K ∧ () ∈ fibreAnchorChoices S Q m n b) →
      ∀ P : FiniteLocusCandidate Λ X → Prop,
        (∃ b : ℂ, b ∈ K ∧ ∃ a : FiniteAnchorCandidate Λ η X S Q m n b,
          P (anchorCandidateLocus Λ η X S Q m n b a)) ↔
        (∃ a : FibreEnumeratedAnchorCandidate Λ η X S Q m n K Z,
          P (fibreEnumeratedAnchorLocus Λ η X S Q m n K Z a)) := by
  classical
  constructor
  · let hf := fibre_coordinates_finite S hS Q m n hQ hne K hK
    exact ⟨hf.toFinset, fun b => hf.mem_toFinset⟩
  intro Z hZ P
  constructor
  · rintro ⟨b, hb, a, ha⟩
    rcases a with a | a
    · exact ⟨.inl (), ha⟩
    rcases a with a | ⟨p, β⟩
    · have hf : () ∈ fibreAnchorChoices S Q m n b :=
        (Subsingleton.elim a.val ()) ▸ a.property
      exact ⟨.inr (.inl ⟨b, (hZ b).mpr ⟨hb, hf⟩⟩), ha⟩
    · exact ⟨.inr (.inr ⟨p, ⟨b, hb⟩, β⟩), ha⟩
  · rintro ⟨a, ha⟩
    rcases a with a | a
    · exact ⟨0, h0, .inl (), ha⟩
    rcases a with b | ⟨p, b, β⟩
    · have hb := (hZ b.val).mp b.property
      exact ⟨b.val, hb.1, .inr (.inl ⟨(), hb.2⟩), ha⟩
    · exact ⟨b.val, b.property, .inr (.inr ⟨p, β⟩), ha⟩
