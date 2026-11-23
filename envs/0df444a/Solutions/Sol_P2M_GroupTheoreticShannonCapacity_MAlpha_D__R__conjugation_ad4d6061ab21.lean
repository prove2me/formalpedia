-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:44:06.119474+00:00
-- url     : https://prove2.me/submissions/a8c786dc-62af-42da-ac88-12b0c3fca972

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (α β : ℝ) (hβ : β ≠ 0) :
    Dα n β * Rα n α * (Dα n β)⁻¹ = β • Rα n (α * β⁻¹^n) := by
  rw [Dα_inv n β hβ]
  ext i j
  simp only [Matrix.mul_apply, Dα, Rα, Matrix.diagonal_apply, Matrix.of_apply,
             Matrix.smul_apply, smul_eq_mul]
  -- The LHS is ∑_x (∑_k (if i=k then β^i else 0) * R_α[k,x]) * (if x=j then β⁻¹^x else 0)
  -- Only k=i contributes in inner sum, only x=j in outer, giving:
  -- β^i * R_α[i,j] * β^{-j}
  -- First simplify the outer sum (only x = j contributes)
  rw [Finset.sum_eq_single j]
  · -- Main term: x = j
    simp only [ite_true]
    -- Now simplify the inner sum (only x_1 = i contributes)
    rw [Finset.sum_eq_single i]
    · -- Main term: x_1 = i
      simp only [ite_true]
      -- Now case split on which entry of R_α we're computing
      by_cases hcorner : i.val = 0 ∧ j.val = n - 1
      · -- Corner case: (0, n-1)
        obtain ⟨hi0, hjn⟩ := hcorner
        simp only [hi0, hjn, and_self, ite_true]
        have hn_pos : 0 < n := by
          by_contra h
          push_neg at h
          have hn0 : n = 0 := Nat.le_zero.mp h
          subst hn0
          exact i.elim0
        -- LHS: β^0 * (-α) * β^{-(n-1)} = -α * β^{-(n-1)}
        -- RHS: β * (-(α * β^{-n})) = -α * β^{1-n}
        simp only [pow_zero, one_mul]
        have key : -α * β⁻¹ ^ (n - 1) = β * -(α * β⁻¹ ^ n) := by
          have h1 : β⁻¹ ^ n = β⁻¹ * β⁻¹ ^ (n - 1) := by
            conv_lhs => rw [← Nat.succ_pred_eq_of_pos hn_pos, pow_succ]
            simp only [Nat.pred_eq_sub_one, mul_comm]
          rw [h1]
          field_simp
        exact key
      · -- Not corner case
        simp only [hcorner, ite_false]
        by_cases hsubdiag : i.val = j.val + 1
        · -- Subdiagonal case
          simp only [hsubdiag, ite_true]
          -- LHS: β^{j+1} * 1 * β^{-j} = β
          -- RHS: β * 1 = β
          simp only [mul_one, pow_succ, mul_comm (β ^ (j : ℕ)), mul_assoc, ← mul_pow]
          simp only [inv_mul_cancel₀ hβ, one_pow, mul_one]
        · -- Other case: entry is 0
          simp only [hsubdiag, ite_false, mul_zero, zero_mul]
    · intro x _ hxi
      simp only [hxi.symm, ↓reduceIte, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro x _ hxj
    simp only [hxj, ↓reduceIte, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
end GroupTheoreticShannonCapacity.MAlpha
