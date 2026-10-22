-- Prove2me | solution 1 for ZhangBSDE.Scheme.lemma_5_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:13:18.639976+00:00
-- url     : https://prove2.me/submissions/f0a1803a-b7b7-49d9-8b3d-6df9edd0961f

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting
set_option autoImplicit false
open MeasureTheory Filter Topology Set ZhangBSDE.Scheme
open scoped NNReal ENNReal

theorem solution {T : ℝ≥0} (π : Partition T) (C : ℝ) (hC : 0 ≤ C) (a b : ℕ → ℝ)
    (ha : 0 ≤ a π.n) (hb : ∀ i ≤ π.n, 0 ≤ b i)
    (hrec : ∀ i ∈ Finset.Icc 1 π.n, a (i - 1) ≤ (1 + C * π.Δt i) * a i + b i) :
    ∀ i ≤ π.n, a i ≤ Real.exp (C * T) * (a π.n + ∑ j ∈ Finset.Icc 1 π.n, b j) := by
  have htt_mono : ∀ k l : ℕ, k ≤ l → π.tt k ≤ π.tt l := by
    intro k l hkl
    unfold Partition.tt
    apply π.mono.monotone
    show min k π.n ≤ min l π.n
    exact min_le_min hkl le_rfl
  have htt_n : π.tt π.n = T := by
    unfold Partition.tt
    have : (⟨min π.n π.n, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (π.n + 1)) = Fin.last π.n := by
      ext; simp
    rw [this]; exact π.finish
  have htt_le : ∀ k, π.tt k ≤ T := by
    intro k
    have h : π.tt k ≤ π.tt π.n := by
      unfold Partition.tt
      apply π.mono.monotone
      show min k π.n ≤ min π.n π.n
      rw [min_self]; exact min_le_right _ _
    rw [htt_n] at h; exact h
  have hΔ : ∀ i, 1 ≤ i → 0 ≤ π.Δt i := by
    intro i h1
    unfold Partition.Δt
    have h := htt_mono (i - 1) i (by omega)
    have h' : ((π.tt (i - 1) : ℝ≥0) : ℝ) ≤ (π.tt i : ℝ) := by exact_mod_cast h
    linarith
  have hT0 : ∀ k, (0:ℝ) ≤ (π.tt k : ℝ) := fun k => NNReal.coe_nonneg _
  have hTle : ∀ k, (π.tt k : ℝ) ≤ (T : ℝ) := fun k => by exact_mod_cast htt_le k
  have hTn : (π.tt π.n : ℝ) = (T : ℝ) := by rw [htt_n]
  set U : ℕ → ℝ := fun i => Real.exp (C * ((π.tt π.n : ℝ) - π.tt i)) *
    (a π.n + ∑ j ∈ Finset.Icc (i + 1) π.n, b j) with hU
  have claim : ∀ d i, i + d = π.n → a i ≤ U i := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have : i = π.n := by omega
      subst this
      simp [hU]
    | succ d ih =>
      intro i hi
      have hi1 : i + 1 ≤ π.n := by omega
      have IH := ih (i + 1) (by omega)
      have hr := hrec (i + 1) (Finset.mem_Icc.mpr ⟨by omega, hi1⟩)
      simp only [Nat.add_sub_cancel] at hr
      have hD := hΔ (i + 1) (by omega)
      have hDdef : π.Δt (i + 1) = (π.tt (i + 1) : ℝ) - π.tt i := by
        unfold Partition.Δt; simp
      set Δ := π.Δt (i + 1) with hΔdef
      have hsplit : ∑ j ∈ Finset.Icc (i + 1) π.n, b j = b (i + 1) + ∑ j ∈ Finset.Icc (i + 1 + 1) π.n, b j := by
        have e : Finset.Icc (i + 1) π.n = insert (i + 1) (Finset.Icc (i + 1 + 1) π.n) := by
          ext j; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        rw [e, Finset.sum_insert (by simp)]
      have hP : 0 ≤ a π.n + ∑ j ∈ Finset.Icc (i + 1 + 1) π.n, b j := by
        apply add_nonneg ha
        apply Finset.sum_nonneg
        intro j hj
        exact hb j (Finset.mem_Icc.mp hj).2
      have hb1 : 0 ≤ b (i + 1) := hb _ hi1
      set P := a π.n + ∑ j ∈ Finset.Icc (i + 1 + 1) π.n, b j with hPdef
      set E1 := Real.exp (C * ((π.tt π.n : ℝ) - π.tt (i + 1))) with hE1
      have hE1ge : 1 ≤ E1 := by
        rw [hE1]
        apply Real.one_le_exp
        apply mul_nonneg hC
        rw [hTn]; linarith [hTle (i + 1)]
      set X := Real.exp (C * Δ) with hX
      have hXge : 1 ≤ X := Real.one_le_exp (mul_nonneg hC hD)
      have hUi1 : U (i + 1) = E1 * P := rfl
      have hUi : U i = X * E1 * (P + b (i + 1)) := by
        show Real.exp (C * ((π.tt π.n : ℝ) - π.tt i)) * (a π.n + ∑ j ∈ Finset.Icc (i + 1) π.n, b j) = _
        rw [hsplit]
        have : Real.exp (C * ((π.tt π.n : ℝ) - π.tt i)) = X * E1 := by
          rw [hX, hE1, ← Real.exp_add]
          congr 1
          rw [hDdef]; ring
        rw [this, hPdef]; ring
      rw [hUi1] at IH
      have h1 : 0 ≤ 1 + C * Δ := by nlinarith [mul_nonneg hC hD]
      have h2 : 1 + C * Δ ≤ X := by
        have := Real.add_one_le_exp (C * Δ)
        linarith
      have hEP : 0 ≤ E1 * P := mul_nonneg (by linarith) hP
      calc a i ≤ (1 + C * Δ) * a (i + 1) + b (i + 1) := hr
        _ ≤ (1 + C * Δ) * (E1 * P) + b (i + 1) := by
            have := mul_le_mul_of_nonneg_left IH h1
            linarith
        _ ≤ X * (E1 * P) + b (i + 1) := by
            have := mul_le_mul_of_nonneg_right h2 hEP
            linarith
        _ ≤ X * (E1 * P) + X * E1 * b (i + 1) := by
            have h3 : 1 ≤ X * E1 := by nlinarith
            have := mul_le_mul_of_nonneg_right h3 hb1
            linarith
        _ = U i := by rw [hUi]; ring
  intro i hi
  have h1 := claim (π.n - i) i (by omega)
  refine h1.trans ?_
  have hnn : 0 ≤ a π.n + ∑ j ∈ Finset.Icc 1 π.n, b j := by
    apply add_nonneg ha
    apply Finset.sum_nonneg
    intro j hj
    exact hb j (Finset.mem_Icc.mp hj).2
  have hsub : ∑ j ∈ Finset.Icc (i + 1) π.n, b j ≤ ∑ j ∈ Finset.Icc 1 π.n, b j := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢
      omega
    · intro j hj _
      exact hb j (Finset.mem_Icc.mp hj).2
  show Real.exp (C * ((π.tt π.n : ℝ) - π.tt i)) * (a π.n + ∑ j ∈ Finset.Icc (i + 1) π.n, b j) ≤ _
  apply mul_le_mul _ (by linarith) _ (Real.exp_pos _).le
  · apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left _ hC
    rw [hTn]; linarith [hT0 i]
  · apply add_nonneg ha
    apply Finset.sum_nonneg
    intro j hj
    exact hb j (by have := (Finset.mem_Icc.mp hj).2; omega)
