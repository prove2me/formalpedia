-- Prove2me | solution 1 for UnderstandingML.linear_multiclass_ndim
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T20:24:33.551093+00:00
-- url     : https://prove2.me/submissions/b82d02ae-83cc-4c71-8323-0d7e3b99e0b2

import Definitions.Def_UnderstandingML_MulticlassLearnability

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

namespace LinearNdimAux

/-- The argmax with smallest-label tie-breaking maximizes the score, strictly beating all smaller
labels. -/
lemma argmaxMin_spec {X : Type*} {d k : ℕ} [NeZero k] (Ψ : X → Fin k → Vec d) (w : Vec d)
    (x : X) :
    (∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x (argmaxMin Ψ w x)⟫_ℝ) ∧
      ∀ j, j < argmaxMin Ψ w x → ⟪w, Ψ x j⟫_ℝ < ⟪w, Ψ x (argmaxMin Ψ w x)⟫_ℝ := by
  classical
  have hne : (Finset.univ.filter (fun i ↦ ∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x i⟫_ℝ)).Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ⟪w, Ψ x i⟫_ℝ)
      Finset.univ_nonempty
    exact ⟨i, by simpa using fun j ↦ hi j (Finset.mem_univ j)⟩
  have heq : argmaxMin Ψ w x =
      (Finset.univ.filter (fun i ↦ ∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x i⟫_ℝ)).min' hne := by
    unfold argmaxMin
    rw [dif_pos hne]
  have hmem := Finset.min'_mem _ hne
  rw [← heq] at hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  refine ⟨hmem, fun j hj ↦ ?_⟩
  by_contra hcon
  push_neg at hcon
  have hj' : j ∈ Finset.univ.filter (fun i ↦ ∀ j, ⟪w, Ψ x j⟫_ℝ ≤ ⟪w, Ψ x i⟫_ℝ) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun l ↦ (hmem l).trans hcon
  have := Finset.min'_le _ _ hj'
  rw [← heq] at this
  exact absurd hj (not_lt.2 this)

/-- A finite family of vectors in `ℝ^d` whose sign patterns under homogeneous halfspaces realize
every subset has at most `d` members. -/
lemma card_le_of_halfspace_shatter {d : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec d)
    (h : ∀ B : Set ι, ∃ w : Vec d, ∀ i, (0 < ⟪w, v i⟫_ℝ ↔ i ∈ B)) : Fintype.card ι ≤ d := by
  by_contra hcon
  push_neg at hcon
  have hli : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    rw [finrank_euclideanSpace_fin] at this
    omega
  obtain ⟨g, hg, i₀, hi₀⟩ := Fintype.not_linearIndependent_iff.1 hli
  -- normalize so that some coefficient is positive
  obtain ⟨g, hg, i₀, hi₀⟩ : ∃ g : ι → ℝ, ∑ i, g i • v i = 0 ∧ ∃ i, 0 < g i := by
    rcases lt_or_gt_of_ne hi₀ with hlt | hgt
    · refine ⟨-g, ?_, i₀, by simp; linarith⟩
      simp [neg_smul, Finset.sum_neg_distrib, hg]
    · exact ⟨g, hg, i₀, hgt⟩
  obtain ⟨w, hw⟩ := h {i | 0 < g i}
  have hzero : ∑ i, g i * ⟪w, v i⟫_ℝ = 0 := by
    have : ⟪w, ∑ i, g i • v i⟫_ℝ = 0 := by rw [hg, inner_zero_right]
    rw [inner_sum] at this
    simpa [inner_smul_right] using this
  have hnn : ∀ i, 0 ≤ g i * ⟪w, v i⟫_ℝ := by
    intro i
    by_cases hi : 0 < g i
    · exact mul_nonneg hi.le ((hw i).2 hi).le
    · have h1 : ⟪w, v i⟫_ℝ ≤ 0 := by
        by_contra h2; push_neg at h2; exact hi ((hw i).1 h2)
      exact mul_nonneg_of_nonpos_of_nonpos (not_lt.1 hi) h1
  have hpos : 0 < g i₀ * ⟪w, v i₀⟫_ℝ := mul_pos hi₀ ((hw i₀).2 hi₀)
  have : 0 < ∑ i, g i * ⟪w, v i⟫_ℝ :=
    Finset.sum_pos' (fun i _ ↦ hnn i) ⟨i₀, Finset.mem_univ _, hpos⟩
  linarith

end LinearNdimAux

end UnderstandingML

open UnderstandingML
open UnderstandingML.LinearNdimAux in
theorem solution {X : Type*} {d k : ℕ} [NeZero k] (Ψ : X → Fin k → Vec d) :
    ndim (linearMulticlassClass Ψ) ≤ d := by
  classical
  unfold ndim
  refine iSup₂_le fun C hC ↦ ?_
  obtain ⟨f₀, f₁, hne, hsh⟩ := hC
  let a : X → Fin k := fun x ↦ max (f₀ x) (f₁ x)
  let b : X → Fin k := fun x ↦ min (f₀ x) (f₁ x)
  let ρ : C → Vec d := fun x ↦ Ψ x (a x) - Ψ x (b x)
  have key : ∀ B' : Set C, ∃ w : Vec d, ∀ x : C, (0 < ⟪w, ρ x⟫_ℝ ↔ x ∈ B') := by
    intro B'
    let B : Finset X := C.filter (fun x ↦ ∃ hx : x ∈ C, (⟨x, hx⟩ ∈ B' ↔ f₀ x = a x))
    obtain ⟨h, hH, h0, h1⟩ := hsh B (Finset.filter_subset _ _)
    obtain ⟨w, rfl⟩ := hH
    refine ⟨w, fun x ↦ ?_⟩
    obtain ⟨x, hx⟩ := x
    have hab : b x < a x := by
      have := hne x hx
      rcases lt_or_gt_of_ne this with hlt | hgt
      · simp [a, b, hlt.le, hlt]
      · simp [a, b, hgt.le, hgt]
    have hval : argmaxMin Ψ w x = a x ↔ (⟨x, hx⟩ : C) ∈ B' := by
      by_cases hB : x ∈ B
      · rw [h0 x hB]
        simp only [B, Finset.mem_filter] at hB
        obtain ⟨-, hx', hiff⟩ := hB
        exact hiff.symm
      · rw [h1 x hx hB]
        have hnot : ¬ ((⟨x, hx⟩ : C) ∈ B' ↔ f₀ x = a x) := by
          intro hc; exact hB (Finset.mem_filter.2 ⟨hx, hx, hc⟩)
        have hf01 : f₁ x = a x ↔ ¬ f₀ x = a x := by
          have := hne x hx
          constructor
          · intro h1 h0; exact this (h0.trans h1.symm)
          · intro h0
            simp only [a] at h0 ⊢
            rcases le_total (f₀ x) (f₁ x) with hle | hle
            · simp [hle]
            · exact absurd (max_eq_left hle).symm h0
        rw [hf01]
        tauto
    have hspec := argmaxMin_spec Ψ w x
    have hmem : argmaxMin Ψ w x = a x ∨ argmaxMin Ψ w x = b x := by
      by_cases hB : x ∈ B
      · rw [h0 x hB]
        rcases le_total (f₀ x) (f₁ x) with hle | hle
        · right; simp [b, hle]
        · left; simp [a, hle]
      · rw [h1 x hx hB]
        rcases le_total (f₀ x) (f₁ x) with hle | hle
        · left; simp [a, hle]
        · right; simp [b, hle]
    simp only [ρ, inner_sub_right]
    rw [← hval]
    constructor
    · intro hpos
      rcases hmem with hm | hm
      · exact hm
      · have := hspec.1 (a x)
        rw [hm] at this
        linarith
    · intro hm
      have := hspec.2 (b x) (hm ▸ hab)
      rw [hm] at this
      linarith
  have := card_le_of_halfspace_shatter ρ key
  rw [Fintype.card_coe] at this
  exact_mod_cast this
