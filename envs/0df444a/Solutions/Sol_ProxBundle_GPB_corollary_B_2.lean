-- Prove2me | solution 1 for ProxBundle.GPB.corollary_B_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T04:14:09.022108+00:00
-- url     : https://prove2.me/submissions/915761f8-796e-4bec-ba81-672ff38a84c8

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model

namespace Aux_GPBW31

lemma dec (u : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (h : ∀ j, 1 ≤ j → j ≤ k → u j < u (j - 1)) :
    u k < u 0 := by
  have hle : ∀ j, j ≤ k → u j ≤ u 0 := by
    intro j
    induction j with
    | zero => intro _; exact le_rfl
    | succ j ih =>
      intro hj
      have := h (j + 1) (by omega) hj
      simp only [Nat.add_sub_cancel] at this
      exact le_trans this.le (ih (by omega))
  have := h k hk le_rfl
  exact lt_of_lt_of_le this (hle (k - 1) (by omega))

end Aux_GPBW31

open ProxBundle.GPB in
theorem solution (θ δ : ℝ) (η α : ℕ → ℝ)
    (hθ : 1 ≤ θ) (hδ : 0 < δ)
    (hη : ∀ j, 0 ≤ η j) (hα : ∀ j, 0 ≤ α j)
    (hrec : ∀ j, 1 ≤ j → η j ≤ α (j - 1) - θ * α j + δ) :
    (∀ k : ℕ, 1 ≤ k →
      (if θ = 1 then α 0 / δ
       else min (α 0 / δ)
         (θ / (θ - 1) * Real.log (α 0 * (θ - 1) / δ + 1))) ≤ (k : ℝ) →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ k ∧ η j ≤ 2 * δ) ∧
    (∀ k : ℕ, 1 ≤ k → α k ≤ α 0 + (k : ℝ) * δ) := by
  constructor
  · intro k hk hcond
    by_contra hcon
    push_neg at hcon
    have hstep : ∀ j, 1 ≤ j → j ≤ k → θ * α j < α (j - 1) - δ := by
      intro j h1 h2
      have := hrec j h1
      have := hcon j h1 h2
      linarith
    -- additive telescoping
    have hadd : α 0 / δ ≤ (k : ℝ) → False := by
      intro h
      have hu := Aux_GPBW31.dec (fun j => α j + (j : ℝ) * δ) k hk (fun j h1 h2 => by
        have := hstep j h1 h2
        have hθα : α j ≤ θ * α j := by nlinarith [hα j]
        show α j + (j : ℝ) * δ < α (j - 1) + ((j - 1 : ℕ) : ℝ) * δ
        rw [Nat.cast_sub h1, Nat.cast_one]
        linarith)
      simp only [Nat.cast_zero, zero_mul, add_zero] at hu
      rw [div_le_iff₀ hδ] at h
      linarith [hα k]
    by_cases hθ1 : θ = 1
    · rw [if_pos hθ1] at hcond
      exact hadd hcond
    · rw [if_neg hθ1] at hcond
      rcases min_le_iff.1 hcond with h | h
      · exact hadd h
      · have hθ1' : 1 < θ := lt_of_le_of_ne hθ (Ne.symm hθ1)
        have hθm : 0 < θ - 1 := by linarith
        set c := δ / (θ - 1) with hcdef
        have hc : 0 < c := div_pos hδ hθm
        have hcid : θ * c - δ = c := by rw [hcdef]; field_simp; ring
        have hu := Aux_GPBW31.dec (fun j => (α j + c) * θ ^ j) k hk (fun j h1 h2 => by
          have key := hstep j h1 h2
          obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
          simp only [Nat.add_sub_cancel] at key ⊢
          have hpos : 0 < θ ^ i := pow_pos (by linarith) i
          have : θ * (α (i + 1) + c) < α i + c := by linarith
          rw [pow_succ]
          nlinarith [mul_lt_mul_of_pos_left this hpos])
        simp only [pow_zero, mul_one] at hu
        have hpk : 0 < θ ^ k := pow_pos (by linarith) k
        have h1 : c * θ ^ k < α 0 + c := by nlinarith [hα k]
        set X := α 0 * (θ - 1) / δ + 1 with hX
        have hXc : α 0 + c = c * X := by rw [hX, hcdef]; field_simp <;> ring
        rw [hXc] at h1
        have h2 : θ ^ k < X := lt_of_mul_lt_mul_left h1 hc.le
        have h3 : Real.log (θ ^ k) < Real.log X := Real.log_lt_log hpk h2
        rw [Real.log_pow] at h3
        have h4 := Real.one_sub_inv_le_log_of_pos (by linarith : 0 < θ)
        have h5 : Real.log X ≤ (θ - 1) / θ * k := by
          have hq : 0 < (θ - 1) / θ := div_pos hθm (by linarith)
          have := mul_le_mul_of_nonneg_left h hq.le
          have e : (θ - 1) / θ * (θ / (θ - 1) * Real.log X) = Real.log X := by
            field_simp
          linarith
        have e2 : (θ - 1) / θ = 1 - θ⁻¹ := by field_simp
        rw [e2] at h5
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith [mul_le_mul_of_nonneg_left h4 hk0]
  · intro k _
    induction k with
    | zero => simp
    | succ k ih =>
      have := hrec (k + 1) (by omega)
      simp only [Nat.add_sub_cancel] at this
      have hθα : α (k + 1) ≤ θ * α (k + 1) := by nlinarith [hα (k + 1)]
      have hk : α k ≤ α 0 + (k : ℝ) * δ := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp
        · exact ih h0
      push_cast
      linarith [hη (k + 1)]
