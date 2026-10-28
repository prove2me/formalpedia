-- Prove2me | solution 1 for RegretMatching.Main.piMat_stochastic_diag_pos
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:20:45.241102+00:00
-- url     : https://prove2.me/submissions/8069791c-39ec-47bb-8f0a-ed5b3aed10ab

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

open MeasureTheory ProbabilityTheory Filter Topology

open RegretMatching.Main in
theorem solution
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) (M : ι → ℝ) (hM : ∀ i s, |u i s| ≤ M i)
    (μ : ℝ) (hμ : ∀ i, 2 * M i * ((Fintype.card (S i) : ℝ) - 1) < μ)
    (i : ι) {t : ℕ} (ht : 1 ≤ t) (h : Fin t → (∀ i, S i)) :
    (∀ j : S i, PiMat u μ h i j ∈ stdSimplex ℝ (S i)) ∧
      ∀ j : S i, 1 - 2 * M i * ((Fintype.card (S i) : ℝ) - 1) / μ ≤ PiMat u μ h i j j ∧
        0 < PiMat u μ h i j j := by
  have s0 : ∀ i, S i := fun i => Classical.arbitrary (S i)
  have hM0 : 0 ≤ M i := (abs_nonneg _).trans (hM i s0)
  have hcard1 : (1 : ℝ) ≤ (Fintype.card (S i) : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hμpos : 0 < μ := by
    have := hμ i
    have : 0 ≤ 2 * M i * ((Fintype.card (S i) : ℝ) - 1) := by
      apply mul_nonneg (by linarith) (by linarith)
    linarith
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  have hR : ∀ j k : S i, 0 ≤ regretR u h i j k ∧ regretR u h i j k ≤ 2 * M i := by
    intro j k
    refine ⟨le_max_right _ _, max_le ?_ (by linarith)⟩
    unfold regretD
    have hterm : ∀ τ ∈ Finset.univ.filter (fun τ : Fin t => h τ i = j),
        u i (Function.update (h τ) i k) - u i (h τ) ≤ 2 * M i := by
      intro τ _
      have h1 := hM i (Function.update (h τ) i k)
      have h2 := hM i (h τ)
      have := le_abs_self (u i (Function.update (h τ) i k))
      have := neg_abs_le (u i (h τ))
      linarith
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    have hc : ((Finset.univ.filter (fun τ : Fin t => h τ i = j)).card : ℝ) ≤ t := by
      have := Finset.card_filter_le (Finset.univ : Finset (Fin t)) (fun τ : Fin t => h τ i = j)
      rw [Finset.card_univ, Fintype.card_fin] at this
      exact_mod_cast this
    rw [nsmul_eq_mul] at hsum
    have : (1 / (t : ℝ)) * ∑ τ ∈ Finset.univ.filter (fun τ : Fin t => h τ i = j),
        (u i (Function.update (h τ) i k) - u i (h τ)) ≤ (1 / (t : ℝ)) * (t * (2 * M i)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    calc _ ≤ (1 / (t : ℝ)) * (t * (2 * M i)) := this
      _ = 2 * M i := by field_simp
  have hdiag : ∀ j : S i, PiMat u μ h i j j =
      1 - ∑ k' ∈ Finset.univ.erase j, regretR u h i j k' / μ := by
    intro j; simp [PiMat]
  have hoff : ∀ j k : S i, k ≠ j → PiMat u μ h i j k = regretR u h i j k / μ := by
    intro j k hkj; simp [PiMat, hkj]
  have hbound : ∀ j : S i, 1 - 2 * M i * ((Fintype.card (S i) : ℝ) - 1) / μ ≤
      PiMat u μ h i j j := by
    intro j
    rw [hdiag]
    have hs := Finset.sum_le_card_nsmul (Finset.univ.erase j) (fun k' => regretR u h i j k' / μ)
      (2 * M i / μ) (fun k' _ => div_le_div_of_nonneg_right (hR j k').2 hμpos.le)
    rw [nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos, Nat.cast_one] at hs
    have : 2 * M i * ((Fintype.card (S i) : ℝ) - 1) / μ =
        ((Fintype.card (S i) : ℝ) - 1) * (2 * M i / μ) := by ring
    linarith
  have hpos : ∀ j : S i, 0 < PiMat u μ h i j j := by
    intro j
    have := hbound j
    have : 2 * M i * ((Fintype.card (S i) : ℝ) - 1) / μ < 1 := by
      rw [div_lt_one hμpos]; exact hμ i
    linarith
  refine ⟨fun j => ⟨?_, ?_⟩, fun j => ⟨hbound j, hpos j⟩⟩
  · intro k
    by_cases hkj : k = j
    · subst hkj; exact (hpos k).le
    · rw [hoff j k hkj]; exact div_nonneg (hR j k).1 hμpos.le
  · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hdiag]
    have : ∑ x ∈ Finset.univ.erase j, PiMat u μ h i j x =
        ∑ x ∈ Finset.univ.erase j, regretR u h i j x / μ := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hoff j x (Finset.ne_of_mem_erase hx)
    rw [this]
    ring
