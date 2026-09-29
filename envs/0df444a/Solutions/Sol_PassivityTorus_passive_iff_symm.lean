-- Prove2me | solution 1 for PassivityTorus.passive_iff_symm
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-24T04:28:21.243548+00:00
-- url     : https://prove2.me/submissions/a0121d02-5e71-40de-a5b1-8415b4663075

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

theorem passive_of_symm (q L d : ℕ) [NeZero L]
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ) (hW : ∀ x a, (W x a)ᵀ = W x a)
    (v : Site q L → (Fin d → ℝ)) : power q L d W v = 0 := by
  rw [power_eq]
  simp [hW]

theorem symm_of_passive (q L d : ℕ) [NeZero L] (hL : 3 ≤ L)
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ)
    (h : ∀ v : Site q L → (Fin d → ℝ), power q L d W v = 0) :
    ∀ x a, (W x a)ᵀ = W x a := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 3 := ⟨L - 3, by omega⟩
  intro x a
  have h2 : (1 + 1 : Fin (m + 3)) ≠ 0 := by
    simp only [ne_eq, Fin.ext_iff, Fin.val_add, Fin.val_one, Fin.val_zero]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  -- one step along an axis always changes that coordinate
  have step_ne : ∀ (z : Site q (m + 3)) (b : Fin q), shift z b 1 ≠ z := by
    intro z b e
    have := congrFun e b
    rw [shift_apply_self] at this
    simp at this
  set y := shift x a 1 with hy
  have hxy : y ≠ x := step_ne x a
  -- a step along another axis b from x cannot reach y (they differ at coordinate b)
  have off_axis : ∀ b, b ≠ a → shift x b 1 ≠ y := by
    intro b hb e
    have := congrFun e b
    rw [shift_apply_self, hy, shift_apply_ne _ _ hb] at this
    simp at this
  -- no step from y returns to x
  have from_y : ∀ b, shift y b 1 ≠ x := by
    intro b e
    have := congrFun e b
    by_cases hb : b = a
    · subst hb
      rw [shift_apply_self, hy, shift_apply_self, add_assoc] at this
      exact h2 (by simpa using this)
    · rw [shift_apply_self, hy, shift_apply_ne _ _ hb] at this
      simp at this
  suffices hA : W x a - (W x a)ᵀ = 0 by
    rw [sub_eq_zero] at hA; exact hA.symm
  ext i j
  let v : Site q (m + 3) → Fin d → ℝ :=
    Function.update (Function.update 0 y (Pi.single j 1)) x (Pi.single i 1)
  have vx : v x = Pi.single i 1 := by simp [v]
  have vy : v y = Pi.single j 1 := by simp [v, Function.update_of_ne hxy]
  have v0 : ∀ z, z ≠ x → z ≠ y → v z = 0 := by
    intro z hzx hzy; simp [v, Function.update_of_ne hzx, Function.update_of_ne hzy]
  have hv := h v
  rw [power_eq, Finset.sum_eq_single x] at hv
  · rw [Finset.sum_eq_single a] at hv
    · rw [vx, ← hy, vy] at hv
      simpa [mulVec_single_one, single_dotProduct] using hv
    · intro b _ hb
      rw [v0 _ (step_ne x b) (off_axis b hb), mulVec_zero, dotProduct_zero]
    · simp
  · intro z _ hzx
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hzy : z = y
    · subst hzy
      rw [v0 _ (from_y b) (step_ne _ b), mulVec_zero, dotProduct_zero]
    · rw [v0 z hzx hzy, zero_dotProduct]
  · simp

end PassivityTorusSol

open PassivityTorus PassivityTorusSol

theorem solution (q L d : ℕ) [NeZero L] (hL : 3 ≤ L)
    (W : Site q L → Fin q → Matrix (Fin d) (Fin d) ℝ) :
    (∀ v : Site q L → (Fin d → ℝ), power q L d W v = 0)
      ↔ ∀ x a, (W x a)ᵀ = W x a :=
  ⟨symm_of_passive q L d hL W, fun hW v => passive_of_symm q L d W hW v⟩
