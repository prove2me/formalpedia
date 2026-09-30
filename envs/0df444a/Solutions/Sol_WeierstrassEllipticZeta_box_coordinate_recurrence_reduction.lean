-- Prove2me | solution 1 for WeierstrassEllipticZeta.box_coordinate_recurrence_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T20:24:46.784952+00:00
-- url     : https://prove2.me/submissions/9b2062fd-ece3-4b70-b8b4-12576ac4ba62

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Ideal.Basic

open scoped Classical Pointwise

noncomputable section

theorem solution
    (K σ : Type*) [CommRing K] [Fintype σ] [DecidableEq σ]
    (b : σ →₀ ℕ) (r : σ → MvPolynomial σ K)
    (hsupport : ∀ i : σ, ∀ e ∈ (r i).support, e ≤ Finsupp.single i (b i)) :
    let S := Finset.Iic b
    let B := (Finset.univ.biUnion fun i : σ =>
      S.image (fun d => d + Finsupp.single i 1)) \ S
    ∀ d ∈ B, ∃ q : MvPolynomial σ K, q.support ⊆ S ∧
      ∀ I : Ideal (MvPolynomial σ K),
        (∀ i : σ, MvPolynomial.X i ^ (b i + 1) - r i ∈ I) →
          MvPolynomial.monomial d 1 - q ∈ I := by
  classical
  dsimp only
  intro d hd
  obtain ⟨hd, hnot⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨i, _, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
  have he_le : e ≤ b := Finset.mem_Iic.mp he
  have htop : e i = b i := by
    by_contra hne
    apply hnot
    apply Finset.mem_Iic.mpr
    intro j
    by_cases hji : j = i
    · subst j
      have hi := he_le i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · simpa [Finsupp.single_apply, hji, Ne.symm hji] using he_le j
  have hsplit : e.erase i + Finsupp.single i (b i + 1) = e + Finsupp.single i 1 := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [htop]
    · simp [Finsupp.erase_ne hji, hji]
  have hmonomial : MvPolynomial.monomial (e + Finsupp.single i 1) (1 : K) =
      MvPolynomial.monomial (e.erase i) 1 * MvPolynomial.X i ^ (b i + 1) := by
    rw [← MvPolynomial.monomial_add_single, hsplit]
  refine ⟨MvPolynomial.monomial (e.erase i) 1 * r i, ?_, ?_⟩
  · intro v hv
    obtain ⟨u, hu, t, ht, rfl⟩ :=
      Finset.mem_add.mp (MvPolynomial.support_mul _ _ hv)
    have hu' : u = e.erase i :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hu)
    subst u
    apply Finset.mem_Iic.mpr
    intro j
    have htj := hsupport i t ht j
    by_cases hji : j = i
    · subst j
      simpa only [Finsupp.add_apply, Finsupp.erase_same, zero_add,
        Finsupp.single_eq_same] using htj
    · have htzero : t j = 0 := by
        simpa [Finsupp.single_apply, hji, Ne.symm hji] using htj
      simpa [Finsupp.erase_ne hji, htzero] using he_le j
  · intro I hrel
    rw [hmonomial, ← mul_sub]
    exact I.mul_mem_left _ (hrel i)
