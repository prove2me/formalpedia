-- Prove2me | solution 1 for QAlgorithms.Arunachalam.xorConv_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T08:16:40.906207+00:00
-- url     : https://prove2.me/submissions/a92b6562-0e08-4fba-a2ae-5cb20d87a858

import Definitions.Def_QAlgorithms_Defs_BooleanFourier
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

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

private def had {k : ℕ} : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  Matrix.of fun x Q => sg (x ⬝ᵥ Q)

private lemma had_square {k : ℕ} :
    (had : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ) * had =
      (2 : ℝ)^k • 1 := by
  classical
  ext x y
  change (∑ z : Fin k → ZMod 2, sg (x ⬝ᵥ z) * sg (z ⬝ᵥ y)) = _
  simp_rw [dotProduct_comm _ y]
  rw [char_orth]
  by_cases h : x = y <;> simp [h]

private lemma conv_had {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    xorConvMatrix g * had = had * Matrix.diagonal (fun Q => (2 : ℝ)^k * boolFourier g Q) := by
  classical
  ext x Q
  have shift := Equiv.sum_comp (Equiv.addRight x)
    (fun z : Fin k → ZMod 2 => g z * sg (z ⬝ᵥ Q))
  have hs : (∑ y : Fin k → ZMod 2, g (x+y) * sg (y ⬝ᵥ Q)) =
      sg (x ⬝ᵥ Q) * ∑ z : Fin k → ZMod 2, g z * sg (z ⬝ᵥ Q) := by
    calc
      _ = ∑ y : Fin k → ZMod 2,
          sg (x ⬝ᵥ Q) * (g (y+x) * sg ((y+x) ⬝ᵥ Q)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [add_dotProduct, sg_add]
        have hsq : sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q) = 1 := by
          rw [← sg_add, two_add]
          norm_num [sg]
        rw [add_comm x y]
        calc
          _ = (g (y+x) * sg (y ⬝ᵥ Q)) * (sg (x ⬝ᵥ Q) * sg (x ⬝ᵥ Q)) := by rw [hsq, mul_one]
          _ = _ := by ring
      _ = _ := by
        rw [← Finset.mul_sum]
        exact congrArg (fun t : ℝ => sg (x ⬝ᵥ Q) * t) shift
  change (∑ y : Fin k → ZMod 2, g (x+y) * sg (y ⬝ᵥ Q)) = _
  rw [hs, Matrix.mul_diagonal]
  change sg (x ⬝ᵥ Q) * _ = sg (x ⬝ᵥ Q) * ((2 : ℝ)^k *
    (((2 : ℝ)^k)⁻¹ * ∑ z, g z * sg (Q ⬝ᵥ z)))
  simp_rw [dotProduct_comm Q]
  field_simp

theorem solution {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    (xorConvMatrix g).charpoly =
        ∏ Q : Fin k → ZMod 2, (Polynomial.X - Polynomial.C ((2 : ℝ) ^ k * boolFourier g Q)) ∧
      spectrum ℝ (xorConvMatrix g) = Set.range fun Q => (2 : ℝ) ^ k * boolFourier g Q := by
  classical
  let H : Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ := had
  let J := ((2 : ℝ)^k)⁻¹ • H
  have hJH : J * H = 1 := by
    dsimp [J, H]
    rw [Matrix.smul_mul, had_square, smul_smul]
    simp
  have hHJ : H * J = 1 := by
    dsimp [J, H]
    rw [Matrix.mul_smul, had_square, smul_smul]
    simp
  have hp : (xorConvMatrix g).charpoly =
      (Matrix.diagonal (fun Q => (2 : ℝ)^k * boolFourier g Q)).charpoly := by
    calc
      _ = ((xorConvMatrix g * H) * J).charpoly := by rw [mul_assoc, hHJ, mul_one]
      _ = (J * (xorConvMatrix g * H)).charpoly := Matrix.charpoly_mul_comm _ _
      _ = (J * (H * Matrix.diagonal (fun Q => (2 : ℝ)^k * boolFourier g Q))).charpoly := by
        rw [show xorConvMatrix g * H = H * Matrix.diagonal (fun Q => (2 : ℝ)^k * boolFourier g Q) from conv_had g]
      _ = _ := by rw [← mul_assoc, hJH, one_mul]
  have hc := hp.trans (Matrix.charpoly_diagonal _)
  refine ⟨hc, ?_⟩
  ext r
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hc]
  simp only [Polynomial.IsRoot, Polynomial.eval_prod, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff,
    Finset.mem_univ, true_and, sub_eq_zero, Set.mem_range]
  constructor <;> rintro ⟨Q, h⟩ <;> exact ⟨Q, h.symm⟩
