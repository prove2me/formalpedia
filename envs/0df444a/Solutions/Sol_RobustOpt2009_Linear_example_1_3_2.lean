-- Prove2me | solution 1 for RobustOpt2009.Linear.example_1_3_2
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T06:44:33.54947+00:00
-- url     : https://prove2.me/submissions/2dc4e7fb-1e1a-42c6-ac3e-8b063a369eb2

import Definitions.Def_RobustOpt2009_Linear_Model

open Matrix
open scoped BigOperators
open RobustOpt2009.Linear

theorem g78l_robust_iff {n L : ℕ} (D : Data n L) (Z : Set (Fin L → ℝ)) (x : Fin n → ℝ) :
    Robust D Z x ↔ ∀ z ∈ Z, D.a0 ⬝ᵥ x + ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) ≤ D.b0 := by
  unfold Robust
  refine forall₂_congr fun z _ => ?_
  have : ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) = ∑ l, z l * (D.a l ⬝ᵥ x) - ∑ l, z l * D.b l := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [this]; constructor <;> intro h <;> linarith

theorem solution {n L : ℕ} (D : Data n L) (x : Fin n → ℝ) :
    (Robust D {z | ∀ l, |z l| ≤ 1} x ↔
      D.a0 ⬝ᵥ x + ∑ l, |D.a l ⬝ᵥ x - D.b l| ≤ D.b0) ∧
    (D.a0 ⬝ᵥ x + ∑ l, |D.a l ⬝ᵥ x - D.b l| ≤ D.b0 ↔
      ∃ v : Fin L → ℝ, (∀ l, -v l ≤ D.a l ⬝ᵥ x - D.b l ∧
        D.a l ⬝ᵥ x - D.b l ≤ v l) ∧ D.a0 ⬝ᵥ x + ∑ l, v l ≤ D.b0) := by
  refine ⟨?_, ?_⟩
  · rw [g78l_robust_iff]
    constructor
    · intro h
      have := h (fun l => if 0 ≤ D.a l ⬝ᵥ x - D.b l then 1 else -1) (fun l => by
        simp only; split_ifs <;> simp)
      convert this using 2
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs with hl
      · rw [abs_of_nonneg hl, one_mul]
      · rw [abs_of_neg (lt_of_not_ge hl)]; ring
    · intro h z hz
      refine le_trans ?_ h
      have : ∑ l, z l * (D.a l ⬝ᵥ x - D.b l) ≤ ∑ l, |D.a l ⬝ᵥ x - D.b l| := by
        refine Finset.sum_le_sum fun l _ => ?_
        calc z l * (D.a l ⬝ᵥ x - D.b l) ≤ |z l * (D.a l ⬝ᵥ x - D.b l)| := le_abs_self _
          _ = |z l| * |D.a l ⬝ᵥ x - D.b l| := abs_mul _ _
          _ ≤ 1 * |D.a l ⬝ᵥ x - D.b l| := mul_le_mul_of_nonneg_right (hz l) (abs_nonneg _)
          _ = _ := one_mul _
      linarith
  · constructor
    · intro h
      exact ⟨fun l => |D.a l ⬝ᵥ x - D.b l|, fun l => ⟨neg_abs_le _, le_abs_self _⟩, h⟩
    · rintro ⟨v, hv, h⟩
      refine le_trans ?_ h
      have : ∑ l, |D.a l ⬝ᵥ x - D.b l| ≤ ∑ l, v l :=
        Finset.sum_le_sum fun l _ => abs_le.2 ⟨(hv l).1, (hv l).2⟩
      linarith
