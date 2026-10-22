-- Prove2me | solution 1 for RevConvexDisj.MultiTerm.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:14:53.512584+00:00
-- url     : https://prove2.me/submissions/62317dff-a25f-465b-91d4-1f22730b0c87

import Mathlib
set_option autoImplicit false

theorem solution (s : ℕ) (a c : Fin s → ℝ) (ha : ∀ i, 0 ≤ a i) (hc : ∀ i, 0 ≤ c i)
    (hsum : 0 < ∑ i, a i) :
    ∃ θ : Fin (s + 1) → ℝ, (∀ i, 0 ≤ θ i) ∧ ∑ i, θ i = 1 ∧
      ∀ i : Fin s, a i * θ 0 - c i * θ i.succ = 0 := by
  by_cases hbad : ∃ i, c i = 0 ∧ 0 < a i
  · obtain ⟨i₀, hc0, _⟩ := hbad
    refine ⟨fun j => if j = i₀.succ then 1 else 0, ?_, ?_, ?_⟩
    · intro j; dsimp only; split_ifs <;> norm_num
    · rw [Fin.sum_univ_succ]
      simp [(Fin.succ_ne_zero i₀).symm, Fin.succ_inj]
    · intro i
      have h0 : (0 : Fin (s + 1)) ≠ i₀.succ := (Fin.succ_ne_zero i₀).symm
      simp only [if_neg h0]
      by_cases h : i = i₀
      · subst h; simp [hc0]
      · have : i.succ ≠ i₀.succ := fun e => h (Fin.succ_injective _ e)
        simp [this]
  · push_neg at hbad
    set r : Fin s → ℝ := fun j => if c j = 0 then 0 else a j / c j with hr
    have hr0 : ∀ j, 0 ≤ r j := by
      intro j; simp only [hr]; split_ifs
      · exact le_rfl
      · exact div_nonneg (ha j) (hc j)
    have hS : 0 ≤ ∑ j, r j := Finset.sum_nonneg (fun j _ => hr0 j)
    have hden : 0 < 1 + ∑ j, r j := by linarith
    set θ0 := 1 / (1 + ∑ j, r j) with hθ0
    have hθ0pos : 0 < θ0 := by positivity
    refine ⟨Fin.cons θ0 (fun j => r j * θ0), ?_, ?_, ?_⟩
    · intro j
      refine Fin.cases ?_ ?_ j
      · simpa using hθ0pos.le
      · intro i; simpa using mul_nonneg (hr0 i) hθ0pos.le
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← Finset.sum_mul, hθ0]
      field_simp
    · intro i
      simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases h : c i = 0
      · have : a i = 0 := le_antisymm (hbad i h) (ha i)
        simp [h, this]
      · simp only [hr, if_neg h]
        field_simp
        ring
