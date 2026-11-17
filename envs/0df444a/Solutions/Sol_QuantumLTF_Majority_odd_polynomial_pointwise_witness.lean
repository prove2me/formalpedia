-- Prove2me | solution 1 for QuantumLTF.Majority.odd_polynomial_pointwise_witness
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-17T02:58:59.053709+00:00
-- url     : https://prove2.me/submissions/cecdbb06-a2e9-4020-8075-00a1302ade3e

import Mathlib
namespace QuantumLTF.Majority

theorem odd_polynomial_pointwise_witness : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ ∀ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2) ≤ C * (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) := by
  refine ⟨2, by norm_num, fun r hr hodd => ?_⟩
  let E : Fin (r+1) → Prop := fun t => (t : ℕ) = 0 ∨ (t : ℕ) = r
  let p : Fin (r+1) → ℝ := fun t => if (t : ℕ) = 0 ∨ (t : ℕ) = r then 1 else 0
  let q : Fin (r+1) → ℝ := fun t => if (t : ℕ) = 0 ∨ (t : ℕ) = r then 1/2 else
    ((r.choose t : ℝ) * (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ) : ℝ))⁻¹
  have hr0 : (0:ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  refine ⟨p, q, ?_, ?_, ?_, ?_⟩
  · simp [p, q]
  · intro t h1 h2
    have hne : ¬ ((t : ℕ) = 0 ∨ (t : ℕ) = r) := by omega
    have hc : (0:ℝ) < r.choose t := by exact_mod_cast Nat.choose_pos (by omega)
    simp only [p, q, if_neg hne]
    simp only [true_iff]
    apply inv_ne_zero
    positivity
  · rw [Fintype.sum_eq_add (0 : Fin (r+1)) (Fin.last r)]
    · simp only [p, q, Fin.val_zero, Fin.val_last, true_or, or_true, if_true, pow_zero,
        Nat.choose_zero_right, Nat.choose_self, hodd.neg_one_pow]
      norm_num
    · intro h; have := congrArg Fin.val h; simp at this; omega
    · intro t ⟨h0, hl⟩
      have h0' : (t : ℕ) ≠ 0 := fun h => h0 (Fin.ext h)
      have hl' : (t : ℕ) ≠ r := fun h => hl (Fin.ext (by simpa using h))
      have hne : ¬ ((t : ℕ) = 0 ∨ (t : ℕ) = r) := by omega
      have hp : p t = 0 := by simp only [p]; exact if_neg hne
      rw [hp]; ring
  · intro t
    have ht : (t : ℕ) ≤ r := Nat.lt_succ_iff.1 t.2
    have hD : (1:ℝ) ≤ (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ) : ℝ) := by
      have : 1 ≤ ((t : ℕ) + 1) * (r - (t : ℕ) + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
      exact_mod_cast this
    set D : ℝ := (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ) : ℝ) with hDdef
    have hDpos : 0 < D := by linarith
    by_cases hE : (t : ℕ) = 0 ∨ (t : ℕ) = r
    · simp only [p, q, if_pos hE]
      have hch : r.choose t = 1 := by rcases hE with h | h <;> simp [h]
      have hDval : D = (r:ℝ) + 1 := by
        rw [hDdef]; rcases hE with h | h <;> simp [h] <;> push_cast <;> ring
      rw [hch, hDval, le_div_iff₀ (by positivity)]
      have : (3:ℝ) ≤ r := by exact_mod_cast hr
      push_cast; nlinarith
    · simp only [p, q, if_neg hE]
      have hc : (1:ℝ) ≤ r.choose t := by exact_mod_cast Nat.choose_pos ht
      rw [le_div_iff₀ hDpos]
      have hcD : 1 ≤ (r.choose t : ℝ) * D := by nlinarith
      have hq : (r.choose t : ℝ) * (0 ^ 2 + ((r.choose t : ℝ) * D)⁻¹ ^ 2) * D
          = ((r.choose t : ℝ) * D)⁻¹ := by
        field_simp
        ring
      rw [hq]
      have : ((r.choose t : ℝ) * D)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hcD
      have : (3:ℝ) ≤ r := by exact_mod_cast hr
      linarith

end QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 3 ≤ r → Odd r → ∃ p q : Fin (r+1) → ℝ, p 0 * q 0 = 1/2 ∧ (∀ t : Fin (r+1), 1 ≤ (t : ℕ) → (t : ℕ) < r → (p t = 0 ↔ q t ≠ 0)) ∧ (∑ t : Fin (r+1), (r.choose t : ℝ) * ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 ∧ ∀ t : Fin (r+1), (r.choose t : ℝ) * (p t^2 + q t^2) ≤ C * (r : ℝ) / (((t : ℕ) + 1 : ℕ) * (r - (t : ℕ) + 1 : ℕ)) :=
  QuantumLTF.Majority.odd_polynomial_pointwise_witness
