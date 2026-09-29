-- Prove2me | solution 1 for PassivityTorus.passive_of_symm
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T04:27:48.572547+00:00
-- url     : https://prove2.me/submissions/c747db46-e532-4a86-ac83-6a31275a1afe

import Mathlib
import Definitions.Def_PassivityTorus_power

open Matrix BigOperators

namespace PassivityTorusSol
open PassivityTorus

theorem shift_apply_self {q L : ℕ} (x : Site q L) (a : Fin q) (s : Fin L) :
    shift x a s a = x a + s := by simp [shift]

theorem shift_apply_ne {q L : ℕ} (x : Site q L) {a b : Fin q} (s : Fin L) (h : b ≠ a) :
    shift x a s b = x b := by simp [shift, h]

theorem shift_back_forward {q L : ℕ} [NeZero L] (x : Site q L) (a : Fin q) :
    shift (shift x a (-1)) a 1 = x := by
  funext b
  by_cases h : b = a
  · subst h; simp [shift]
  · simp [shift, h]

theorem shift_forward_back {q L : ℕ} [NeZero L] (x : Site q L) (a : Fin q) :
    shift (shift x a 1) a (-1) = x := by
  funext b
  by_cases h : b = a
  · subst h; simp [shift]
  · simp [shift, h]

/-- One step forward along axis a, as a bijection of the sites. -/
def stepEquiv {q L : ℕ} [NeZero L] (a : Fin q) : Site q L ≃ Site q L where
  toFun x := shift x a 1
  invFun x := shift x a (-1)
  left_inv x := shift_forward_back x a
  right_inv x := shift_back_forward x a

theorem power_eq (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ)
    (v : Site q L → (Fin d → ℝ)) :
    power q L d W v =
      ∑ x : Site q L, ∑ a : Fin q, v x ⬝ᵥ ((W x a - (W x a)ᵀ) *ᵥ v (shift x a 1)) := by
  have key : ∀ a : Fin q,
      ∑ x : Site q L, v x ⬝ᵥ (W (shift x a (-1)) a *ᵥ v (shift x a (-1)))
        = ∑ x : Site q L, v x ⬝ᵥ ((W x a)ᵀ *ᵥ v (shift x a 1)) := by
    intro a
    rw [← Equiv.sum_comp (stepEquiv a)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [stepEquiv, Equiv.coe_fn_mk, shift_forward_back]
    rw [dotProduct_mulVec (v y), vecMul_transpose, dotProduct_comm]
  unfold power
  simp only [dotProduct_sub, Finset.sum_sub_distrib, sub_mulVec]
  congr 1
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => key a

end PassivityTorusSol

open PassivityTorus PassivityTorusSol

theorem solution (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ) (hW : ∀ x a, (W x a)ᵀ = W x a)
    (v : Site q L → (Fin d → ℝ)) : power q L d W v = 0 := by
  rw [power_eq]
  simp [hW]
