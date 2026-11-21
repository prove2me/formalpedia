-- Prove2me | solution 1 for OnlineCarpoolingLei.Oblivious.positive_affine_combination
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T13:27:27.450354+00:00
-- url     : https://prove2.me/submissions/d02ad458-f22c-4e7d-8ea5-0e046657e3d0

import Mathlib

open Set

theorem solution {N m : ℕ} (B : Set (Fin N → ℝ)) (hB_ne : B.Nonempty)
    (hB_compact : IsCompact B) (hB_convex : Convex ℝ B)
    (ϕ : Fin m → (Fin N → ℝ) →ᵃ[ℝ] ℝ)
    (hcover : B = ⋃ i, {p | p ∈ B ∧ 0 < ϕ i p}) :
    ∃ lam : Fin m → ℝ, (∀ i, 0 ≤ lam i) ∧ ∀ p ∈ B, 0 < ∑ i, lam i * ϕ i p := by
  classical
  rcases isEmpty_or_nonempty (Fin m) with hem | hne
  · have hB_empty : B = ∅ := by
      rw [hcover]
      exact Set.iUnion_of_empty _
    exact absurd hB_empty hB_ne.ne_empty
  · let Φ : (Fin N → ℝ) →ᵃ[ℝ] (Fin m → ℝ) := AffineMap.pi ϕ
    let K : Set (Fin m → ℝ) := Φ '' B
    let C : Set (Fin m → ℝ) := {y | ∀ i, y i ≤ 0}
    have hΦapply : ∀ (p : Fin N → ℝ) (i : Fin m), Φ p i = ϕ i p := fun p i =>
      AffineMap.pi_apply ϕ p i
    have hΦcont : Continuous Φ := AffineMap.continuous_of_finiteDimensional Φ
    have hKconv : Convex ℝ K := hB_convex.affine_image Φ
    have hKcomp : IsCompact K := hB_compact.image hΦcont
    have hCconv : Convex ℝ C := by
      intro x hx y hy a b ha hb _hab i
      exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (hx i))
        (mul_nonpos_of_nonneg_of_nonpos hb (hy i))
    have hCclosed : IsClosed C := by
      have hCeq : C = ⋂ i, {y : Fin m → ℝ | y i ≤ 0} := by
        ext y
        simp [C]
      rw [hCeq]
      exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
    have hdisj : Disjoint K C := by
      rw [Set.disjoint_left]
      rintro y ⟨p, hpB, rfl⟩ hyC
      have hp : p ∈ ⋃ i, {p : Fin N → ℝ | p ∈ B ∧ 0 < ϕ i p} := by
        rw [← hcover]
        exact hpB
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hp
      obtain ⟨i, -, hpos⟩ := hp
      have hle := hyC i
      rw [hΦapply p i] at hle
      linarith
    obtain ⟨f, u, v, hKu, huv, hCv⟩ :=
      geometric_hahn_banach_compact_closed hKconv hKcomp hCconv hCclosed hdisj
    have h0C : (0 : Fin m → ℝ) ∈ C := by
      intro i
      simp
    have hv0 : v < 0 := by
      have h := hCv 0 h0C
      simpa using h
    have hCnn : ∀ y ∈ C, 0 ≤ f y := by
      intro y hy
      by_contra hneg
      have hneg' : f y < 0 := lt_of_not_ge hneg
      set t : ℝ := v / f y + 1 with ht
      have htpos : 0 < t := by
        have h1 : 0 < v / f y := div_pos_of_neg_of_neg hv0 hneg'
        rw [ht]
        linarith
      have htC : t • y ∈ C := by
        intro i
        have hi := hy i
        simp only [Pi.smul_apply, smul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos htpos.le hi
      have hlt := hCv (t • y) htC
      have hft : f (t • y) = t * f y := by
        rw [map_smul, smul_eq_mul]
      rw [hft] at hlt
      have htfy : t * f y = v + f y := by
        rw [ht, add_mul, one_mul, div_mul_cancel₀ v (ne_of_lt hneg')]
      rw [htfy] at hlt
      linarith
    let lam : Fin m → ℝ := fun i => -f (Pi.single i 1)
    have hlam_nonneg : ∀ i, 0 ≤ lam i := by
      intro i
      have hmem : (-(Pi.single i (1 : ℝ) : Fin m → ℝ)) ∈ C := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Pi.neg_apply, Pi.single_eq_of_ne hji]
          simp
      have h := hCnn _ hmem
      simpa [lam] using h
    have hrepr : ∀ y : Fin m → ℝ, f y = ∑ i, f (Pi.single i 1) * y i := by
      intro y
      have hy : y = ∑ i, y i • Pi.single i (1 : ℝ) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hy]
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul]
      ring
    refine ⟨lam, hlam_nonneg, ?_⟩
    intro p hpB
    have hKp : Φ p ∈ K := ⟨p, hpB, rfl⟩
    have hflt : f (Φ p) < 0 := lt_trans (hKu (Φ p) hKp) (lt_trans huv hv0)
    have hsum : ∑ i, lam i * ϕ i p = -f (Φ p) := by
      have hΦp : f (Φ p) = ∑ i, f (Pi.single i 1) * ϕ i p := by
        have := hrepr (fun i => ϕ i p)
        rwa [show (fun i => ϕ i p) = Φ p from funext fun i => (hΦapply p i).symm] at this
      have h1 : ∑ i, lam i * ϕ i p = -∑ i, f (Pi.single i 1) * ϕ i p := by
        simp only [lam]
        rw [← Finset.sum_neg_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [h1, ← hΦp]
    rw [hsum]
    linarith
