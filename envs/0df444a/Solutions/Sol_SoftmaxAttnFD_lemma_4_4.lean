-- Prove2me | solution 1 for SoftmaxAttnFD.lemma_4_4
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-22T12:45:42.332797+00:00
-- url     : https://prove2.me/submissions/a1dbe491-e91c-4a24-b94e-5b19d61e62f8

import Mathlib

theorem solution (n : ℕ) (hn : 1 ≤ n) (k : Fin n → Fin 2 → ℝ) (C : Set (Fin 2 → ℝ))
    (hC : C = convexHull ℝ (Set.range k)) (h0 : (0 : Fin 2 → ℝ) ∈ interior C)
    (ρ : Fin n → ℝ) (kb : Fin n → Fin 2 → ℝ)
    (hρ : ∀ j, k j ≠ 0 → 0 < ρ j ∧ ρ j ≤ 1 ∧ k j = ρ j • kb j ∧ kb j ∈ frontier C)
    (q : Fin 2 → ℝ) (h L : ℝ) (hL : 0 < L) (hh : h = ⨆ j, q ⬝ᵥ k j) (hhL : L < h)
    (Ki : Set (Fin n))
    (hKi : Ki = {j | k j ≠ 0 ∧ 1 - L / h ≤ ρ j ∧ h - L ≤ q ⬝ᵥ kb j}) :
    {j | h - L ≤ q ⬝ᵥ k j} ⊆ Ki ∧ Ki ⊆ {j | h - 2 * L ≤ q ⬝ᵥ k j} := by
  classical
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hhpos : 0 < h := lt_trans hL hhL
  -- every `q ⬝ᵥ k j` is at most `h`
  have hle : ∀ j : Fin n, q ⬝ᵥ k j ≤ h := by
    intro j
    rw [hh]
    exact le_ciSup (Set.finite_range (fun j : Fin n => q ⬝ᵥ k j)).bddAbove j
  -- the half-space `{x | q ⬝ᵥ x ≤ h}` is convex
  have hconv : Convex ℝ {x : Fin 2 → ℝ | q ⬝ᵥ x ≤ h} := by
    rw [convex_iff_add_mem]
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have h1 : a * (q ⬝ᵥ x) ≤ a * h := mul_le_mul_of_nonneg_left hx ha
    have h2 : b * (q ⬝ᵥ y) ≤ b * h := mul_le_mul_of_nonneg_left hy hb
    nlinarith
  -- `C` lies in the half-space
  have hCsub : C ⊆ {x : Fin 2 → ℝ | q ⬝ᵥ x ≤ h} := by
    rw [hC]
    exact convexHull_min (fun x hx => by rcases hx with ⟨j, rfl⟩; exact hle j) hconv
  -- `C` is closed, hence its frontier lies in `C`
  have hclosed : IsClosed C := by
    rw [hC]
    exact (Set.Finite.isCompact_convexHull ℝ (Set.finite_range k)).isClosed
  have hfront : frontier C ⊆ C := by
    have h1 : frontier C ⊆ closure C := frontier_subset_closure
    rwa [hclosed.closure_eq] at h1
  have hkb_le : ∀ j, k j ≠ 0 → q ⬝ᵥ kb j ≤ h := by
    intro j hj
    exact hCsub (hfront (hρ j hj).2.2.2)
  constructor
  · -- left inclusion: `{j | h - L ≤ q ⬝ᵥ k j} ⊆ Ki`
    intro j hj
    have hj' : h - L ≤ q ⬝ᵥ k j := by simpa using hj
    have hneq : k j ≠ 0 := by
      intro hzero
      have hz : q ⬝ᵥ k j = 0 := by rw [hzero, dotProduct_zero]
      linarith
    obtain ⟨hρpos, hρle, hksmul, hkbfront⟩ := hρ j hneq
    have hdot : q ⬝ᵥ k j = ρ j * (q ⬝ᵥ kb j) := by
      rw [hksmul, dotProduct_smul, smul_eq_mul]
    have hkbpos : 0 < q ⬝ᵥ kb j := by
      have hpos : 0 < q ⬝ᵥ k j := by linarith
      rw [hdot] at hpos
      nlinarith [hρpos]
    rw [hKi]
    simp only [Set.mem_setOf_eq]
    refine ⟨hneq, ?_, ?_⟩
    · -- `1 - L/h ≤ ρ j`
      have hkey : h - L ≤ ρ j * h := by
        calc h - L ≤ q ⬝ᵥ k j := hj'
          _ = ρ j * (q ⬝ᵥ kb j) := hdot
          _ ≤ ρ j * h := mul_le_mul_of_nonneg_left (hkb_le j hneq) hρpos.le
      have hdiv : (h - L) / h ≤ ρ j := by
        rw [div_le_iff₀ hhpos]
        linarith
      have heq : 1 - L / h = (h - L) / h := by
        rw [← div_sub_div_same, div_self hhpos.ne']
      rw [heq]
      exact hdiv
    · -- `h - L ≤ q ⬝ᵥ kb j`
      have hmul : ρ j * (q ⬝ᵥ kb j) ≤ q ⬝ᵥ kb j :=
        mul_le_of_le_one_left hkbpos.le hρle
      linarith
  · -- right inclusion: `Ki ⊆ {j | h - 2 * L ≤ q ⬝ᵥ k j}`
    intro j hj
    rw [hKi] at hj
    simp only [Set.mem_setOf_eq] at hj
    obtain ⟨hneq, hρlb, hkblb⟩ := hj
    obtain ⟨hρpos, hρle, hksmul, hkbfront⟩ := hρ j hneq
    have hdot : q ⬝ᵥ k j = ρ j * (q ⬝ᵥ kb j) := by
      rw [hksmul, dotProduct_smul, smul_eq_mul]
    simp only [Set.mem_setOf_eq]
    have h1 : ρ j * (h - L) ≤ q ⬝ᵥ k j := by
      rw [hdot]
      exact mul_le_mul_of_nonneg_left hkblb hρpos.le
    have h2 : (1 - L / h) * (h - L) ≤ ρ j * (h - L) :=
      mul_le_mul_of_nonneg_right hρlb (by linarith)
    have h3 : h - 2 * L ≤ (1 - L / h) * (h - L) := by
      have heq : (1 - L / h) * (h - L) = h - 2 * L + L ^ 2 / h := by
        field_simp [hhpos.ne']
        ring
      rw [heq]
      have hnonneg : 0 ≤ L ^ 2 / h := div_nonneg (sq_nonneg L) hhpos.le
      linarith
    linarith
