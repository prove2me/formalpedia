-- Prove2me | solution 1 for TeschlODE.Stability.tendsto_infDist_omegaLimitSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T06:33:16.69483+00:00
-- url     : https://prove2.me/submissions/cc2f76b2-9da0-4fe5-a7f1-cd64c41dc57f

import Mathlib
import Definitions.Def_TeschlODE_Stability_IsIntegralCurve
import Definitions.Def_TeschlODE_Stability_IsMaximalFlow
import Definitions.Def_TeschlODE_Stability_semiOrbit
import Definitions.Def_TeschlODE_Stability_omegaLimitSet

set_option autoImplicit false

open TeschlODE.Stability in
theorem dea7652b_mem_I {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n)))
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (hne : (omegaLimitSet M σ I Φ x).Nonempty) (s : ℝ) (hs : 0 < s) :
    σ * s ∈ I x := by
  obtain ⟨⟨_, hJ, _, _⟩, h0, _, _⟩ := hΦ x hx
  obtain ⟨y, _, t, ht, htt, _⟩ := hne
  obtain ⟨k, hk⟩ := (htt.eventually (Filter.eventually_gt_atTop s)).exists
  rcases hσ with rfl | rfl
  · rw [one_mul] at hk ⊢
    exact hJ.out h0 (ht k) ⟨hs.le, hk.le⟩
  · have hk' : t k < -s := by linarith
    have : -1 * s = -s := by ring
    rw [this]
    exact hJ.out (ht k) h0 ⟨hk'.le, by linarith⟩

open TeschlODE.Stability in
theorem solution {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : IsOpen M) (hf : ContDiffOn ℝ 1 f M)
    (I : EuclideanSpace ℝ (Fin n) → Set ℝ)
    (Φ : ℝ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hΦ : IsMaximalFlow f M I Φ)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ M)
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : IsCompact C) (hCM : C ⊆ M)
    (horb : semiOrbit σ I Φ x ⊆ C) :
    Filter.Tendsto (fun t : ℝ => Metric.infDist (Φ (σ * t) x) (omegaLimitSet M σ I Φ x))
      Filter.atTop (nhds 0) := by
  have hσσ : ∀ r : ℝ, σ * (σ * r) = r := by
    intro r; rcases hσ with rfl | rfl <;> ring
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra hcon
  push_neg at hcon
  choose s hsN hsP using hcon
  have hdist : ∀ r : ℝ, ε ≤ Metric.infDist (Φ (σ * s r) x) (omegaLimitSet M σ I Φ x) := by
    intro r
    have := hsP r
    rwa [Real.dist_0_eq_abs, abs_of_nonneg Metric.infDist_nonneg] at this
  have hne : (omegaLimitSet M σ I Φ x).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have := hdist 0
    rw [h, Metric.infDist_empty] at this
    linarith
  let a : ℕ → ℝ := fun k => s ((k : ℝ) + 1)
  have ha_pos : ∀ k, 0 < a k := by
    intro k
    have := hsN ((k : ℝ) + 1)
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    show 0 < s ((k : ℝ) + 1)
    linarith
  have ha : Filter.Tendsto a Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun k => ?_) tendsto_natCast_atTop_atTop
    have := hsN ((k : ℝ) + 1)
    show (k : ℝ) ≤ s ((k : ℝ) + 1)
    linarith
  have hmemI : ∀ k, σ * a k ∈ I x := fun k =>
    dea7652b_mem_I f M I Φ hΦ σ hσ x hx hne (a k) (ha_pos k)
  have hmemC : ∀ k, Φ (σ * a k) x ∈ C := by
    intro k
    apply horb
    exact ⟨σ * a k, hmemI k, by rw [hσσ]; exact ha_pos k, rfl⟩
  obtain ⟨y, hyC, φ, hφ, hlim⟩ := hC.tendsto_subseq hmemC
  have hyΩ : y ∈ omegaLimitSet M σ I Φ x := by
    refine ⟨hCM hyC, fun k => σ * a (φ k), fun k => hmemI (φ k), ?_, hlim⟩
    exact (ha.comp hφ.tendsto_atTop).congr (fun k => (hσσ _).symm)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hlim ε hε
  have h1 := hN N le_rfl
  have h2 := Metric.infDist_le_dist_of_mem (x := Φ (σ * a (φ N)) x) hyΩ
  have h3 := hdist ((φ N : ℝ) + 1)
  simp only [Function.comp] at h1
  have : ε < ε := lt_of_le_of_lt h3 (lt_of_le_of_lt h2 h1)
  exact lt_irrefl _ this
