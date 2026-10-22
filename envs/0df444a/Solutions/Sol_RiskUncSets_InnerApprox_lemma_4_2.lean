-- Prove2me | solution 1 for RiskUncSets.InnerApprox.lemma_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:01:04.032889+00:00
-- url     : https://prove2.me/submissions/d560ac24-ba1c-41b8-89ee-c520e5e53042

import Mathlib
import Definitions.Def_RiskUncSets_InnerApprox_Setting
noncomputable section


namespace RiskUncSets.InnerApprox

open scoped Pointwise

lemma gen_mix {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (lam : ℝ)
    (τ : Equiv.Perm (Fin N)) :
    ∑ i, mix q lam (τ i) • a i =
      lam • ∑ i, q (τ i) • a i + (1 - lam) • sampleMean a := by
  unfold mix sampleMean
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_smul, mul_smul, mul_smul]

lemma permutohull_mix {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (lam : ℝ) :
    permutohull (mix q lam) a =
      (fun x => lam • x + (1 - lam) • sampleMean a) '' permutohull q a := by
  let f : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    (lam • LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] _).toAffineMap +
      AffineMap.const ℝ _ ((1 - lam) • sampleMean a)
  have hf : ∀ x, f x = lam • x + (1 - lam) • sampleMean a := by
    intro x; simp [f]
  have : (fun x => lam • x + (1 - lam) • sampleMean a) = f := by
    funext x; exact (hf x).symm
  rw [this, permutohull, permutohull, AffineMap.image_convexHull]
  congr 1
  ext y
  simp only [Set.mem_range, Set.mem_image]
  constructor
  · rintro ⟨τ, rfl⟩
    exact ⟨_, ⟨τ, rfl⟩, by rw [hf, gen_mix]⟩
  · rintro ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact ⟨τ, by rw [hf, gen_mix]⟩

lemma piTilde_mix {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) (lam : ℝ) :
    piTilde (mix q lam) a = lam • piTilde q a := by
  ext w
  simp only [piTilde, permutohull_mix, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x - sampleMean a, ⟨x, hx, rfl⟩, ?_⟩
    simp only [smul_sub, smul_eq_mul]
    module
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨lam • x + (1 - lam) • sampleMean a, ⟨x, hx, rfl⟩, ?_⟩
    simp only [smul_sub]
    module

lemma permutohull_symm {N n : ℕ} (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N)
    (a : Fin N → Fin n → ℝ) : ∀ y ∈ permutohull q a, (2 : ℝ) • sampleMean a - y ∈ permutohull q a := by
  obtain ⟨-, σ, hσ⟩ := hq
  have hgen : ∀ τ : Equiv.Perm (Fin N),
      (2 : ℝ) • sampleMean a - ∑ i, q (τ i) • a i = ∑ i, q ((τ.trans σ) i) • a i := by
    intro τ
    have h1 : ∀ i, q (τ i) = 2 / (N : ℝ) - q (σ (τ i)) := fun i => by
      conv_lhs => rw [hσ]
    have h2 : ∑ i, q (τ i) • a i = (2 : ℝ) • sampleMean a - ∑ i, q (σ (τ i)) • a i := by
      unfold sampleMean
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1 i, sub_smul, smul_smul]
      congr 2
      ring
    rw [h2]
    simp [Equiv.trans_apply]
  let g : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    ((-1 : ℝ) • LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] _).toAffineMap +
      AffineMap.const ℝ _ ((2 : ℝ) • sampleMean a)
  have hg : ∀ x, g x = (2 : ℝ) • sampleMean a - x := by
    intro x; simp [g]; abel
  have hconv : Convex ℝ (g ⁻¹' permutohull q a) :=
    (convex_convexHull ℝ _).affine_preimage g
  intro y hy
  have : permutohull q a ⊆ g ⁻¹' permutohull q a := by
    apply convexHull_min _ hconv
    rintro _ ⟨τ, rfl⟩
    show g _ ∈ permutohull q a
    rw [hg, hgen]
    exact subset_convexHull ℝ _ ⟨_, rfl⟩
  have := this hy
  simpa [hg] using this

lemma piTilde_symm {N n : ℕ} (q : Fin N → ℝ) (hq : q ∈ symRestrictedSimplex N)
    (a : Fin N → Fin n → ℝ) : ∀ x ∈ piTilde q a, -x ∈ piTilde q a := by
  rintro _ ⟨y, hy, rfl⟩
  refine ⟨(2 : ℝ) • sampleMean a - y, permutohull_symm q hq a y hy, ?_⟩
  simp only
  module

theorem lemma_4_2_core {N n : ℕ} (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (lam : ℝ) :
    ∀ w : Fin n → ℝ, normQ (mix q lam) a w = (1 / |lam|) * normQ q a w := by
  intro w
  unfold normQ
  rw [piTilde_mix, gauge_smul_left (piTilde_symm q hq a)]
  simp [one_div]

end RiskUncSets.InnerApprox

open RiskUncSets.InnerApprox


theorem solution {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (lam : ℝ) (hlam : lam ≠ 0) :
    ∀ w : Fin n → ℝ, normQ (mix q lam) a w = (1 / |lam|) * normQ q a w := by
  exact lemma_4_2_core q hq a lam
