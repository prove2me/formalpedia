-- Prove2me | solution 1 for WeierstrassEllipticZeta.monomial_border_completion
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T02:18:20.694057+00:00
-- url     : https://prove2.me/submissions/81d4a1cf-3da0-403a-a5d4-928df032c6cf

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Data.Finset.Union

noncomputable section

theorem solution
    (K σ : Type*) [Field K] [Fintype σ] [DecidableEq σ]
    (S : Finset (σ →₀ ℕ)) (b : (σ →₀ ℕ) → MvPolynomial σ K) :
    let B := (Finset.univ.biUnion fun i : σ =>
      S.image (fun d => d + Finsupp.single i 1)) \ S
    (∀ e ∈ B, (b e).support ⊆ S) →
    ∃ r : σ → (σ →₀ ℕ) → MvPolynomial σ K,
      (∀ i : σ, ∀ d ∈ S, (r i d).support ⊆ S) ∧
      ∀ I : Ideal (MvPolynomial σ K),
        (∀ e ∈ B, MvPolynomial.monomial e 1 - b e ∈ I) ↔
          ∀ i : σ, ∀ d ∈ S,
            MvPolynomial.X i * MvPolynomial.monomial d 1 - r i d ∈ I := by
  classical
  let B := (Finset.univ.biUnion fun i : σ =>
    S.image (fun d => d + Finsupp.single i 1)) \ S
  change (∀ e ∈ B, (b e).support ⊆ S) → _
  intro hsupport
  let r : σ → (σ →₀ ℕ) → MvPolynomial σ K := fun i d =>
    if d + Finsupp.single i 1 ∈ S then MvPolynomial.monomial (d + Finsupp.single i 1) 1
    else b (d + Finsupp.single i 1)
  have hprod (i : σ) (d : σ →₀ ℕ) :
      MvPolynomial.X i * MvPolynomial.monomial d (1 : K) =
        MvPolynomial.monomial (d + Finsupp.single i 1) 1 := by
    rw [MvPolynomial.monomial_add_single, pow_one, mul_comm]
  have hborder (i : σ) (d : σ →₀ ℕ) (hd : d ∈ S)
      (hnot : d + Finsupp.single i 1 ∉ S) : d + Finsupp.single i 1 ∈ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨d, hd, rfl⟩⟩, hnot⟩
  refine ⟨r, ?_, ?_⟩
  · intro i d hd
    dsimp only [r]
    split_ifs with h
    · exact MvPolynomial.support_monomial_subset.trans (Finset.singleton_subset_iff.mpr h)
    · exact hsupport _ (hborder i d hd h)
  · intro I
    constructor
    · intro hb i d hd
      by_cases h : d + Finsupp.single i 1 ∈ S
      · simpa only [hprod, r, if_pos h, sub_self] using I.zero_mem
      · simpa only [hprod, r, if_neg h] using hb _ (hborder i d hd h)
    · intro hr e he
      obtain ⟨he, hnot⟩ := Finset.mem_sdiff.mp he
      obtain ⟨i, _, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
      simpa only [hprod, r, if_neg hnot] using hr i d hd
