-- Prove2me | solution 1 for PassivityRing.symm_of_passive
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T22:01:34.415533+00:00
-- url     : https://prove2.me/submissions/f380b3d3-a35a-4f0b-b03f-d0f7ae67bb23

import Mathlib
import Definitions.Def_PassivityRing_power

open Matrix BigOperators

namespace PassivityRingSol
open PassivityRing

theorem power_eq (N d : ℕ) [NeZero N]
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ) (v : Fin N → (Fin d → ℝ)) :
    power N d W v = ∑ i : Fin N, v i ⬝ᵥ ((W i - (W i)ᵀ) *ᵥ v (i + 1)) := by
  unfold power
  have key : ∑ i : Fin N, v i ⬝ᵥ (W (i - 1) *ᵥ v (i - 1))
      = ∑ i : Fin N, v i ⬝ᵥ ((W i)ᵀ *ᵥ v (i + 1)) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin N))]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [dotProduct_mulVec (v j), vecMul_transpose, dotProduct_comm]
  simp only [dotProduct_sub, Finset.sum_sub_distrib, sub_mulVec, key]

end PassivityRingSol

open PassivityRing PassivityRingSol

theorem solution (N d : ℕ) [NeZero N] (hN : 3 ≤ N)
    (W : Fin N → Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ v : Fin N → (Fin d → ℝ), power N d W v = 0) :
    ∀ i, (W i)ᵀ = W i := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  intro i
  have h1 : (1 : Fin (k + 3)) ≠ 0 := by simp
  have h2 : (1 + 1 : Fin (k + 3)) ≠ 0 := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have hi1 : i + 1 ≠ i := by intro e; simp at e
  have hi2 : i + 1 + 1 ≠ i := by
    intro e; apply h2; rw [add_assoc] at e; simpa using e
  have hi21 : i + 1 + 1 ≠ i + 1 := by intro e; simp at e
  suffices hA : W i - (W i)ᵀ = 0 by rw [sub_eq_zero] at hA; exact hA.symm
  ext a b
  let v : Fin (k + 3) → (Fin d → ℝ) :=
    Function.update (Function.update 0 (i + 1) (Pi.single b 1)) i (Pi.single a 1)
  have hv := h v
  rw [power_eq, Finset.sum_eq_single i] at hv
  · simp only [v, Function.update_self, Function.update_of_ne hi1] at hv
    simpa [mulVec_single_one, single_dotProduct] using hv
  · intro j _ hj
    by_cases hj1 : j = i + 1
    · subst hj1
      have : v (i + 1 + 1) = 0 := by
        simp [v, Function.update_of_ne hi2]
      rw [this, mulVec_zero, dotProduct_zero]
    · have : v j = 0 := by simp [v, Function.update_of_ne hj, Function.update_of_ne hj1]
      rw [this, zero_dotProduct]
  · simp
