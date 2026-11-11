-- Prove2me | solution 1 for PauliUnclonable531.Pauli.character_norm
-- status  : ACCEPTED   (prove)
-- author  : @sragavan
-- created : 2026-11-10T10:22:36.220203+00:00
-- url     : https://prove2.me/submissions/1112d62b-5355-4067-92af-739c703123a9

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Symplectic

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli.Character

open PauliUnclonable531.Pauli

lemma sign_add (a b : Fin 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> simp [sign]

lemma sign_sum {ι : Type} (s : Finset ι) (f : ι → Fin 2) :
    sign (∑ i ∈ s, f i) = ∏ i ∈ s, sign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sign]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, sign_add, ih]

lemma qubit_char_sum (c : Fin 2) : (∑ u : Fin 2, sign (c * u)) = if c = 0 then 2 else 0 := by
  fin_cases c <;> simp [sign, Fin.sum_univ_two] <;> norm_num

lemma bits_char_sum {n : ℕ} (c : Bits n) :
    (∑ u : Bits n, ∏ j, sign (c j * u j)) = if c = 0 then (2 : ℂ) ^ n else 0 := by
  rw [← Fintype.prod_sum (fun j (u : Fin 2) => sign (c j * u))]
  simp only [qubit_char_sum]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

lemma char_sum {n : ℕ} (a : Label n) :
    (∑ m : Label n, sign (symplectic a m)) = if a = 0 then (4 : ℂ) ^ n else 0 := by
  have h : ∀ m : Label n, sign (symplectic a m) =
      (∏ j, sign (a.2 j * m.1 j)) * (∏ j, sign (a.1 j * m.2 j)) := by
    intro m
    rw [symplectic, sign_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [sign_add, mul_comm]
  simp only [h]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [bits_char_sum, bits_char_sum]
  rcases a with ⟨a1, a2⟩
  by_cases h1 : a1 = 0 <;> by_cases h2 : a2 = 0 <;> simp [h1, h2, Prod.ext_iff]
  rw [← mul_pow]; norm_num

lemma symplectic_comm {n : ℕ} (k l : Label n) : symplectic k l = symplectic l k := by
  unfold symplectic
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [add_comm, mul_comm (l.2 j), mul_comm (l.1 j)]

lemma symplectic_add_left {n : ℕ} (k l m : Label n) :
    symplectic k m + symplectic l m = symplectic (k + l) m := by
  unfold symplectic
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have key : ∀ a b c d e f : Fin 2,
      a * e + b * f + (c * e + d * f) = (a + c) * e + (b + d) * f := by decide
  exact key _ _ _ _ _ _

lemma add_eq_zero_iff {n : ℕ} (k l : Label n) : k + l = 0 ↔ k = l := by
  have h2 : ∀ x y : Fin 2, x + y = 0 ↔ x = y := by decide
  simp only [Prod.ext_iff, funext_iff, Prod.fst_add, Prod.snd_add, Pi.add_apply, Prod.fst_zero,
    Prod.snd_zero, Pi.zero_apply, h2]

lemma character_herm (n : ℕ) : (character n).conjTranspose = character n := by
  ext k l
  simp only [Matrix.conjTranspose_apply, character]
  rw [symplectic_comm]
  generalize symplectic k l = c
  fin_cases c <;> simp [sign]

lemma character_sq (n : ℕ) : character n * character n = ((4 : ℂ) ^ n) • 1 := by
  ext k l
  simp only [Matrix.mul_apply, character, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [← sign_add, symplectic_comm _ l, symplectic_add_left, char_sum, add_eq_zero_iff]
  split_ifs <;> simp

end PauliUnclonable531.Pauli.Character

open PauliUnclonable531.Pauli PauliUnclonable531.Pauli.Character in
theorem solution (n : ℕ) : PauliUnclonable531.Pauli.spectralNorm (character n) = (2 : ℝ)^n := by
  unfold PauliUnclonable531.Pauli.spectralNorm
  have hsq : ‖character n‖ * ‖character n‖ = (2 : ℝ) ^ n * (2 : ℝ) ^ n := by
    rw [← CStarRing.norm_star_mul_self, Matrix.star_eq_conjTranspose, character_herm, character_sq,
      norm_smul, norm_one, mul_one, norm_pow]
    rw [← mul_pow]
    norm_num
  have h0 : 0 ≤ ‖character n‖ := norm_nonneg _
  have h1 : (0 : ℝ) ≤ 2 ^ n := by positivity
  nlinarith [mul_self_nonneg (‖character n‖ - 2 ^ n), mul_self_nonneg (‖character n‖ + 2 ^ n)]
