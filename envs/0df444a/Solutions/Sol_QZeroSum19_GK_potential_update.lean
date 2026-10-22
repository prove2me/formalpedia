-- Prove2me | solution 1 for QZeroSum19.GK.potential_update
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:53.984743+00:00
-- url     : https://prove2.me/submissions/d9ec1d18-aa33-4673-b8d4-703bf98f9076

import Mathlib
import Definitions.Def_QZeroSum19_GK_Setting
set_option autoImplicit false
open Matrix QZeroSum19.GK

theorem VV_aux {ι : Type*} [Fintype ι] (f g : ι → ℝ) (hf : ∀ j, 0 < f j) :
    (∑ j, f j) * (∑ j, f j / (∑ l, f l) * g j) = ∑ j, f j * g j := by
  by_cases hS : ∑ l, f l = 0
  · rw [hS, zero_mul]
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (hf j).le)).1 hS
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [h0 j hj, zero_mul]
  · have : ∀ j, f j / (∑ l, f l) * g j = (f j * g j) / (∑ l, f l) := fun j => by ring
    simp_rw [this]
    rw [← Finset.sum_div, mul_div_cancel₀ _ hS]

theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ)
    (y : Fin m → ℝ) (η : ℝ) (a : Fin m) (b : Fin n) :
    potential A (x + η • Pi.single b 1) (y + η • Pi.single a 1) =
      potential A x y * (∑ j, gibbs (-(Aᵀ *ᵥ x)) j * Real.exp (-η * A b j)) *
        (∑ i, gibbs (A *ᵥ y) i * Real.exp (η * A i a)) := by
  have hx : ∀ j, (Aᵀ *ᵥ (x + η • Pi.single b 1)) j = (Aᵀ *ᵥ x) j + η * A b j := by
    intro j
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Pi.single_apply]
    ring
  have hy : ∀ i, (A *ᵥ (y + η • Pi.single a 1)) i = (A *ᵥ y) i + η * A i a := by
    intro i
    simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Pi.single_apply]
    ring
  have k1 := VV_aux (fun j => Real.exp (-(Aᵀ *ᵥ x) j)) (fun j => Real.exp (-η * A b j))
    (fun j => Real.exp_pos _)
  have k2 := VV_aux (fun i => Real.exp ((A *ᵥ y) i)) (fun i => Real.exp (η * A i a))
    (fun i => Real.exp_pos _)
  have e1 : ∑ j, Real.exp (-(Aᵀ *ᵥ (x + η • Pi.single b 1)) j)
      = ∑ j, Real.exp (-(Aᵀ *ᵥ x) j) * Real.exp (-η * A b j) := by
    apply Finset.sum_congr rfl; intro j _
    rw [hx j, ← Real.exp_add]; congr 1; ring
  have e2 : ∑ i, Real.exp ((A *ᵥ (y + η • Pi.single a 1)) i)
      = ∑ i, Real.exp ((A *ᵥ y) i) * Real.exp (η * A i a) := by
    apply Finset.sum_congr rfl; intro i _
    rw [hy i, Real.exp_add]
  unfold potential gibbs
  simp only [Pi.neg_apply]
  rw [e1, e2, ← k1, ← k2]
  ring
