-- Prove2me | solution 1 for RankOneBimatrix.BinSearch.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:21:54.280992+00:00
-- url     : https://prove2.me/submissions/6d5f2192-c146-49f4-a126-605c37fe479d

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game

open Matrix

namespace Aux_ROBS

lemma value {ι : Type*} [Fintype ι] (x g : ι → ℝ) (u : ℝ) (hx : x ∈ stdSimplex ℝ ι)
    (hc : ∀ i, x i = 0 ∨ g i = u) : x ⬝ᵥ g = u := by
  have : ∀ i, x i * g i = x i * u := by
    intro i
    rcases hc i with h | h <;> simp [h]
  unfold dotProduct
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.sum_mul, hx.2, one_mul]

lemma br {ι : Type*} [Fintype ι] [DecidableEq ι] (x g : ι → ℝ) (hx : x ∈ stdSimplex ℝ ι) :
    (∀ x' ∈ stdSimplex ℝ ι, x' ⬝ᵥ g ≤ x ⬝ᵥ g) ↔
      ∃ u : ℝ, (∀ i, g i ≤ u) ∧ (∀ i, x i = 0 ∨ g i = u) := by
  constructor
  · intro h
    have hne : (Finset.univ : Finset ι).Nonempty := by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty] at hne
      have := hx.2
      rw [hne, Finset.sum_empty] at this
      exact zero_ne_one this
    obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ g hne
    refine ⟨g i0, fun i => hi0 i (Finset.mem_univ i), fun i => ?_⟩
    have h1 : g i0 ≤ x ⬝ᵥ g := by
      have := h (Pi.single i0 1) (single_mem_stdSimplex ℝ i0)
      rwa [single_one_dotProduct] at this
    have h2 : x ⬝ᵥ g ≤ g i0 := by
      unfold dotProduct
      calc ∑ i, x i * g i ≤ ∑ i, x i * g i0 :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hi0 i (Finset.mem_univ i)) (hx.1 i)
        _ = g i0 := by rw [← Finset.sum_mul, hx.2, one_mul]
    have hsum : ∑ i, x i * (g i0 - g i) = 0 := by
      have : ∑ i, x i * (g i0 - g i) = g i0 - x ⬝ᵥ g := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx.2, one_mul]
        rfl
      rw [this]; linarith
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (hx.1 j) (by linarith [hi0 j (Finset.mem_univ j)]))).mp hsum i (Finset.mem_univ i)
    rcases mul_eq_zero.mp hterm with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (by linarith)
  · rintro ⟨u, hle, hc⟩ x' hx'
    rw [value x g u hx hc]
    unfold dotProduct
    calc ∑ i, x' i * g i ≤ ∑ i, x' i * u :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hle i) (hx'.1 i)
      _ = u := by rw [← Finset.sum_mul, hx'.2, one_mul]

end Aux_ROBS

open RankOneBimatrix.BinSearch in
theorem solution {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    (IsRowBR A x y ↔
      x ∈ Mixed m ∧ y ∈ Mixed n ∧ ∃ u : ℝ,
        (∀ i, (A *ᵥ y) i ≤ u) ∧
        (∀ i, x i = 0 ∨ (A *ᵥ y) i = u)) ∧
    (IsColBR B x y ↔
      x ∈ Mixed m ∧ y ∈ Mixed n ∧ ∃ v : ℝ,
        (∀ j, (B.transpose *ᵥ x) j ≤ v) ∧
        (∀ j, y j = 0 ∨ (B.transpose *ᵥ x) j = v)) ∧
    (∀ u v : ℝ,
      x ∈ Mixed m → y ∈ Mixed n →
      (∀ i, (A *ᵥ y) i ≤ u) →
      (∀ i, x i = 0 ∨ (A *ᵥ y) i = u) →
      (∀ j, (B.transpose *ᵥ x) j ≤ v) →
      (∀ j, y j = 0 ∨ (B.transpose *ᵥ x) j = v) →
      u = x ⬝ᵥ (A *ᵥ y) ∧ v = x ⬝ᵥ (B *ᵥ y)) := by
  have hB : ∀ y' : Fin n → ℝ, x ⬝ᵥ (B *ᵥ y') = y' ⬝ᵥ (B.transpose *ᵥ x) := by
    intro y'
    rw [dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (Aux_ROBS.br x (A *ᵥ y) hx).mp h⟩
    · rintro ⟨hx, hy, h⟩
      exact ⟨hx, hy, (Aux_ROBS.br x (A *ᵥ y) hx).mpr h⟩
  · constructor
    · rintro ⟨hx, hy, h⟩
      refine ⟨hx, hy, (Aux_ROBS.br y (B.transpose *ᵥ x) hy).mp fun y' hy' => ?_⟩
      rw [← hB, ← hB]; exact h y' hy'
    · rintro ⟨hx, hy, h⟩
      refine ⟨hx, hy, fun y' hy' => ?_⟩
      rw [hB, hB]
      exact (Aux_ROBS.br y (B.transpose *ᵥ x) hy).mpr h y' hy'
  · intro u v hx hy _ hcu _ hcv
    refine ⟨(Aux_ROBS.value x _ u hx hcu).symm, ?_⟩
    rw [hB, Aux_ROBS.value y _ v hy hcv]
