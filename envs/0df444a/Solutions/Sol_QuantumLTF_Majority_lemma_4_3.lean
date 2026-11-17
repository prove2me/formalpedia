-- Prove2me | solution 1 for QuantumLTF.Majority.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:12:23.415203+00:00
-- url     : https://prove2.me/submissions/a4a8fbc9-e895-4958-a5ac-adcb4deac084

import Mathlib
namespace QuantumLTF.Majority

theorem lemma_4_3 : ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, 3≤k → Odd k → ∃ P Q : Fin (k+1) → ℝ, (∀ t : Fin (k+1), 1≤t.1 → t.1<k → (P t=0 ↔ Q t≠0)) ∧ ∀ t : Fin (k+1), (k.choose t : ℝ)*(P t^2+Q t^2) ≤ C*(k:ℝ)/((t.1+1)*(k-t.1+1)) := by
  refine ⟨1, one_pos, fun k hk _ => ?_⟩
  refine ⟨fun _ => 0, fun t => 1 / (((t.1 : ℝ) + 1) * ((k : ℝ) - t.1 + 1) * (k.choose t : ℝ)), ?_, ?_⟩
  · intro t _ _
    have htk : (t.1 : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp t.isLt
    have hB : (0 : ℝ) < (k.choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp t.isLt)
    have hD : (0 : ℝ) < ((t.1 : ℝ) + 1) * ((k : ℝ) - t.1 + 1) := by
      apply mul_pos <;> linarith [(Nat.cast_nonneg t.1 : (0 : ℝ) ≤ t.1)]
    simp only [true_iff]
    exact (one_div_pos.mpr (mul_pos hD hB)).ne'
  · intro t
    have htk : (t.1 : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp t.isLt
    have hB1 : (1 : ℝ) ≤ (k.choose t : ℝ) := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp t.isLt)
    have ht0 : (0 : ℝ) ≤ t.1 := Nat.cast_nonneg _
    have hD1 : (1 : ℝ) ≤ ((t.1 : ℝ) + 1) * ((k : ℝ) - t.1 + 1) := by nlinarith
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
    set D := ((t.1 : ℝ) + 1) * ((k : ℝ) - t.1 + 1) with hDdef
    set B := (k.choose t : ℝ) with hBdef
    have hDp : 0 < D := by linarith
    have hBp : 0 < B := by linarith
    have lhs : B * (0 ^ 2 + (1 / (D * B)) ^ 2) = 1 / (D * (D * B)) := by
      rw [zero_pow two_ne_zero, zero_add]
      field_simp
    rw [lhs, one_mul, div_le_div_iff₀ (by positivity) hDp]
    have h1 : 1 ≤ D * B := by nlinarith
    have h2 : D ≤ D * (D * B) := by nlinarith
    have h4 : 0 ≤ D * (D * B) := by positivity
    have h3 : D * (D * B) ≤ k * (D * (D * B)) := by nlinarith
    linarith
end QuantumLTF.Majority

theorem solution : ∃ C : ℝ, 0<C ∧ ∀ k : ℕ, 3≤k → Odd k → ∃ P Q : Fin (k+1) → ℝ, (∀ t : Fin (k+1), 1≤t.1 → t.1<k → (P t=0 ↔ Q t≠0)) ∧ ∀ t : Fin (k+1), (k.choose t : ℝ)*(P t^2+Q t^2) ≤ C*(k:ℝ)/((t.1+1)*(k-t.1+1)) :=
  QuantumLTF.Majority.lemma_4_3
