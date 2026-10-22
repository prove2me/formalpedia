-- Prove2me | solution 1 for RiskUncSets.InnerApprox.proposition_4_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T01:02:35.502368+00:00
-- url     : https://prove2.me/submissions/b1f53ae4-9068-4ce6-89f7-886800b25268

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


lemma piTilde_eq_image {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    piTilde q a = (Homeomorph.subRight (sampleMean a)) '' permutohull q a := rfl

lemma piTilde_convex {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    Convex ℝ (piTilde q a) := by
  let f : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ) :=
    (LinearMap.id : (Fin n → ℝ) →ₗ[ℝ] _).toAffineMap + AffineMap.const ℝ _ (-sampleMean a)
  have : piTilde q a = f '' permutohull q a := by
    unfold piTilde
    congr 1
  rw [this]
  exact (convex_convexHull ℝ _).affine_image f

lemma piTilde_compact {N n : ℕ} (q : Fin N → ℝ) (a : Fin N → Fin n → ℝ) :
    IsCompact (piTilde q a) := by
  rw [piTilde_eq_image]
  refine IsCompact.image ?_ (Homeomorph.subRight (sampleMean a)).continuous
  exact Set.Finite.isCompact_convexHull (𝕜 := ℝ) (Set.finite_range _)

theorem proposition_4_2_core {N n : ℕ} (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (hint : (interior (permutohull q a)).Nonempty) :
    (∀ w : Fin n → ℝ, normQ q a w = 0 ↔ w = 0) ∧
    (∀ (β : ℝ) (w : Fin n → ℝ), normQ q a (β • w) = |β| * normQ q a w) ∧
    ∀ w₁ w₂ : Fin n → ℝ, normQ q a (w₁ + w₂) ≤ normQ q a w₁ + normQ q a w₂ := by
  have hsym : piTilde q a = -piTilde q a := by
    apply Set.Subset.antisymm
    · intro x hx
      exact piTilde_symm q hq a x hx |> fun h => by simpa using h
    · intro x hx
      have := piTilde_symm q hq a (-x) hx
      simpa using this
  have hconv := piTilde_convex q a
  have hint' : (interior (piTilde q a)).Nonempty := by
    rw [piTilde_eq_image, ← Homeomorph.image_interior]
    exact hint.image _
  have h0 : (0 : Fin n → ℝ) ∈ interior (piTilde q a) := by
    obtain ⟨x, hx⟩ := hint'
    have hx' : -x ∈ interior (piTilde q a) := by
      have hsub : (fun y : Fin n → ℝ => -y) ⁻¹' interior (piTilde q a) ⊆ piTilde q a := by
        intro y hy
        have : -y ∈ piTilde q a := interior_subset hy
        have := piTilde_symm q hq a _ this
        simpa using this
      have := interior_maximal hsub (isOpen_interior.preimage continuous_neg)
      exact this (by simpa using hx)
    have := hconv.interior (a := (1/2 : ℝ)) (b := (1/2 : ℝ)) hx hx' (by norm_num) (by norm_num) (by norm_num)
    simpa using this
  have habs : Absorbent ℝ (piTilde q a) := absorbent_nhds_zero (mem_interior_iff_mem_nhds.mp h0)
  have hbdd : Bornology.IsVonNBounded ℝ (piTilde q a) := (NormedSpace.isVonNBounded_iff ℝ).mpr (piTilde_compact q a).isBounded
  refine ⟨fun w => ?_, fun β w => ?_, fun w₁ w₂ => ?_⟩
  · exact gauge_eq_zero habs hbdd
  · unfold normQ
    rcases le_or_gt 0 β with hβ | hβ
    · rw [gauge_smul_of_nonneg hβ, abs_of_nonneg hβ, smul_eq_mul]
    · have e : β • w = -((-β) • w) := by module
      rw [e, gauge_neg (piTilde_symm q hq a), gauge_smul_of_nonneg (by linarith), abs_of_neg hβ,
        smul_eq_mul]
  · exact gauge_add_le hconv habs w₁ w₂

end RiskUncSets.InnerApprox

open RiskUncSets.InnerApprox


theorem solution {N n : ℕ} (hN : 0 < N) (q : Fin N → ℝ)
    (hq : q ∈ symRestrictedSimplex N) (a : Fin N → Fin n → ℝ)
    (hint : (interior (permutohull q a)).Nonempty) :
    (∀ w : Fin n → ℝ, normQ q a w = 0 ↔ w = 0) ∧
    (∀ (β : ℝ) (w : Fin n → ℝ), normQ q a (β • w) = |β| * normQ q a w) ∧
    ∀ w₁ w₂ : Fin n → ℝ, normQ q a (w₁ + w₂) ≤ normQ q a w₁ + normQ q a w₂ := by
  exact proposition_4_2_core q hq a hint
