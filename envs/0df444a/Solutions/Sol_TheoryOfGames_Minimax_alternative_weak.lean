-- Prove2me | solution 1 for TheoryOfGames.Minimax.alternative_weak
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:55:08.21355+00:00
-- url     : https://prove2.me/submissions/3f56bb29-edee-4279-b91e-ba63275a2697

import Mathlib

set_option autoImplicit false

namespace P2M12a41f1e

theorem key {n m : ℕ} (hm : 0 < m) (a : Fin n → Fin m → ℝ)
    (h : ¬ ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) :
    ∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 ≤ ∑ i, a i j * w i := by
  classical
  let L : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := Matrix.mulVecLin (Matrix.of a)
  have hL : ∀ x i, L x i = ∑ j, a i j * x j := by
    intro x i; simp [L, Matrix.mulVec, dotProduct]
  have hKc : IsCompact (L '' stdSimplex ℝ (Fin m)) :=
    (isCompact_stdSimplex ℝ (Fin m)).image L.continuous_of_finiteDimensional
  have hKv : Convex ℝ (L '' stdSimplex ℝ (Fin m)) :=
    (convex_stdSimplex ℝ (Fin m)).linear_image L
  have hdisj : Disjoint (L '' stdSimplex ℝ (Fin m)) (Set.Iic (0 : Fin n → ℝ)) := by
    rw [Set.disjoint_left]
    rintro y ⟨x, hx, rfl⟩ hy
    exact h ⟨x, hx, fun i => by rw [← hL]; exact hy i⟩
  obtain ⟨f, u, v, hfK, huv, hfC⟩ :=
    geometric_hahn_banach_compact_closed hKv hKc (convex_Iic 0) isClosed_Iic hdisj
  have hv : v < 0 := by simpa using hfC 0 (Set.mem_Iic.mpr le_rfl)
  have hfC' : ∀ y : Fin n → ℝ, y ≤ 0 → 0 ≤ f y := by
    intro y hy
    by_contra hneg
    push_neg at hneg
    have ht : 0 < v / f y := div_pos_of_neg_of_neg hv hneg
    have hmem : (v / f y) • y ≤ 0 := smul_nonpos_of_nonneg_of_nonpos ht.le hy
    have h2 := hfC _ (Set.mem_Iic.mpr hmem)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at h2
    exact lt_irrefl _ h2
  set w : Fin n → ℝ := fun i => f (-Pi.single i 1) with hw
  have hw0 : ∀ i, 0 ≤ w i := by
    intro i
    apply hfC'
    intro k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have hfy : ∀ y : Fin n → ℝ, f y = - ∑ i, y i * w i := by
    intro y
    conv_lhs => rw [pi_eq_sum_univ' y]
    simp [w, map_sum, map_smul, map_neg, Finset.sum_neg_distrib]
  have hpos : ∀ j, 0 < ∑ i, a i j * w i := by
    intro j
    have h1 := hfK (L (Pi.single j 1)) ⟨_, single_mem_stdSimplex ℝ j, rfl⟩
    rw [hfy] at h1
    have h3 : ∀ i, L (Pi.single j 1) i = a i j := by
      intro i; rw [hL]; simp [Pi.single_apply]
    simp only [h3] at h1
    linarith
  set S : ℝ := ∑ i, w i with hSdef
  have hS : 0 < S := by
    by_contra hS0
    push_neg at hS0
    have hS1 : S = 0 := le_antisymm hS0 (Finset.sum_nonneg fun i _ => hw0 i)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw0 i)).mp hS1
    have := hpos ⟨0, hm⟩
    simp [hz] at this
  refine ⟨fun i => w i / S, ⟨fun i => div_nonneg (hw0 i) hS.le, ?_⟩, fun j => ?_⟩
  · rw [← Finset.sum_div, div_self hS.ne']
  · have he : ∑ i, a i j * (w i / S) = (∑ i, a i j * w i) / S := by
      rw [Finset.sum_div]; congr 1; ext i; ring
    rw [he]
    exact div_nonneg (hpos j).le hS.le

end P2M12a41f1e

namespace TheoryOfGames.Minimax

theorem alternative_weak' {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : Fin n → Fin m → ℝ) :
    (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) ∨
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 ≤ ∑ i, a i j * w i) := by
  by_cases h : ∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0
  · exact Or.inl h
  · exact Or.inr (P2M12a41f1e.key hm a h)

end TheoryOfGames.Minimax

open TheoryOfGames.Minimax in
theorem solution {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (a : Fin n → Fin m → ℝ) :
    (∃ x ∈ stdSimplex ℝ (Fin m), ∀ i, ∑ j, a i j * x j ≤ 0) ∨
      (∃ w ∈ stdSimplex ℝ (Fin n), ∀ j, 0 ≤ ∑ i, a i j * w i) := by
  exact TheoryOfGames.Minimax.alternative_weak' hn hm a
