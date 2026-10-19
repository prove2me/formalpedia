-- Prove2me | solution 1 for QAlgorithms.Arunachalam.fourier_comp_matrix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:10:42.578908+00:00
-- url     : https://prove2.me/submissions/d4a1a886-3734-471e-b6f3-9fe434c0e120

import Definitions.Def_QAlgorithms_Defs_BooleanFourier

set_option autoImplicit false
open scoped BigOperators
open QAlgorithms

private def sg (a : ZMod 2) : ℝ := (-1 : ℝ) ^ a.val

private lemma bits (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have h : a.val = 0 ∨ a.val = 1 := by have := ZMod.val_lt a; omega
  rcases h with h | h
  · exact Or.inl ((ZMod.val_eq_zero a).mp h)
  · exact Or.inr ((ZMod.val_injective 2) (by simpa only [ZMod.val_one_eq_one_mod] using h))

private lemma sg_add (a b : ZMod 2) : sg (a + b) = sg a * sg b := by
  have h : (1 + 1 : ZMod 2) = 0 := by decide
  rcases bits a with rfl | rfl <;> rcases bits b with rfl | rfl <;>
    norm_num [sg, h, ZMod.val_zero, ZMod.val_one_eq_one_mod, ZMod.val_two_eq_two_mod]

private lemma two_add (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

private lemma vec_two_add {n : ℕ} (a : Fin n → ZMod 2) : a + a = 0 := by
  ext i
  exact two_add (a i)

private lemma add_zero_iff {n : ℕ} (a b : Fin n → ZMod 2) : a + b = 0 ↔ a = b := by
  constructor
  · intro h
    have := congrArg (fun x => x + b) h
    simpa only [add_assoc, vec_two_add, add_zero, zero_add] using this
  · rintro rfl
    exact vec_two_add a

private lemma char_sum {n : ℕ} (a : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) = if a = 0 then (2 : ℝ)^n else 0 := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [sg]
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! h
      exact ha (funext h)
    have hai : a i = 1 := by
      exact (bits (a i)).resolve_left hi
    have shift : (∑ x : Fin n → ZMod 2,
        sg (a ⬝ᵥ (x + (Pi.single i 1 : Fin n → ZMod 2)))) =
        ∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) :=
      Equiv.sum_comp (Equiv.addRight (Pi.single i 1 : Fin n → ZMod 2))
        (fun x : Fin n → ZMod 2 => sg (a ⬝ᵥ x))
    have hs : (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ (x + Pi.single i 1))) =
        -(∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x)) := by
      simp_rw [dotProduct_add, dotProduct_single, mul_one, hai, sg_add]
      norm_num [sg, ZMod.val_one_eq_one_mod, Finset.sum_neg_distrib]
    rw [hs] at shift
    rw [if_neg ha]
    linarith

private lemma char_orth {n : ℕ} (a b : Fin n → ZMod 2) :
    (∑ x : Fin n → ZMod 2, sg (a ⬝ᵥ x) * sg (b ⬝ᵥ x)) =
      if a = b then (2 : ℝ)^n else 0 := by
  simp_rw [← sg_add, ← add_dotProduct]
  rw [char_sum]
  simp only [add_zero_iff]

private lemma inversion {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) (y : Fin n → ZMod 2) :
    f y = ∑ S : Fin n → ZMod 2, boolFourier f S * sg (S ⬝ᵥ y) := by
  classical
  symm
  calc
    _ = ((2 : ℝ)^n)⁻¹ * ∑ x, f x *
        ∑ S : Fin n → ZMod 2, sg (S ⬝ᵥ x) * sg (S ⬝ᵥ y) := by
      simp only [boolFourier]
      change (∑ S, ((2 : ℝ)^n)⁻¹ * (∑ x, f x * sg (S ⬝ᵥ x)) * sg (S ⬝ᵥ y)) = _
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro S _
      ring
    _ = ((2 : ℝ)^n)⁻¹ * (f y * (2 : ℝ)^n) := by
      congr 1
      have h (x : Fin n → ZMod 2) :
          (∑ S : Fin n → ZMod 2, sg (S ⬝ᵥ x) * sg (S ⬝ᵥ y)) =
            if x = y then (2 : ℝ)^n else 0 := by
        simpa only [dotProduct_comm] using char_orth x y
      simp_rw [h]
      simp [mul_ite]
    _ = f y := by field_simp

theorem solution {m k : ℕ} (f : (Fin m → ZMod 2) → ℝ)
    (M : Matrix (Fin m) (Fin k) (ZMod 2)) (Q : Fin k → ZMod 2) :
    boolFourier (fun z => f (M.mulVec z)) Q =
      ∑ S ∈ Finset.univ.filter (fun S : Fin m → ZMod 2 => M.transpose.mulVec S = Q),
        boolFourier f S := by
  classical
  change ((2 : ℝ)^k)⁻¹ * (∑ z, f (M.mulVec z) * sg (Q ⬝ᵥ z)) = _
  calc
    _ = ((2 : ℝ)^k)⁻¹ * ∑ z : Fin k → ZMod 2,
        (∑ S : Fin m → ZMod 2, boolFourier f S * sg (S ⬝ᵥ M.mulVec z)) * sg (Q ⬝ᵥ z) := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      rw [← inversion f (M.mulVec z)]
    _ = ∑ S : Fin m → ZMod 2, boolFourier f S *
        (((2 : ℝ)^k)⁻¹ * ∑ z : Fin k → ZMod 2,
          sg (M.transpose.mulVec S ⬝ᵥ z) * sg (Q ⬝ᵥ z)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro z _
      rw [dotProduct_comm (M.transpose.mulVec S) z,
        Matrix.dotProduct_transpose_mulVec M z S]
      ring
    _ = ∑ S : Fin m → ZMod 2, if M.transpose.mulVec S = Q then boolFourier f S else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      rw [char_orth]
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_filter]
