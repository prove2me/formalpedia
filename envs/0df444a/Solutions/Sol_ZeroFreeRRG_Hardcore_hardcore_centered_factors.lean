-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.hardcore_centered_factors
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:00:53.522892+00:00
-- url     : https://prove2.me/submissions/ee58c5bb-76e2-4316-be52-b702ca13138a

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
import Mathlib
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open scoped Classical BigOperators
open ZeroFreeRRG.Hardcore

private lemma pi0 (a : ℝ) : Model.pi .hardcore a (0 : Fin 2) = 1-a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring
private lemma pi1 (a : ℝ) : Model.pi .hardcore a (1 : Fin 2) = a := by
  simp [Model.pi, Model.Spin, Model.P, Fin.sum_univ_two] <;> ring

/-- Equation (25) for the hardcore cavity interaction and edge factor. -/
theorem solution (a : ℝ) (ha : 0 < a) (ha1 : a < 1 / 2)
    (x y : Fin 2 → ℝ) (hx : (∑ i, x i) = 1) (hy : (∑ i, y i) = 1) :
    let θ := a/(1-a)
    let h := (x 1-a)/(1-a)
    let k := (y 1-a)/(1-a)
    Mmul .hardcore a x (0 : Fin 2) = 1+θ*h ∧
    Mmul .hardcore a x (1 : Fin 2) = 1-h ∧
    edgeFactor .hardcore a x y = 1-h*k := by
  have hane : a ≠ 0 := ne_of_gt ha
  have hne : 1-a ≠ 0 := by linarith
  have hx' : x 0 + x 1 = 1 := by simpa [Fin.sum_univ_two] using hx
  have hy' : y 0 + y 1 = 1 := by simpa [Fin.sum_univ_two] using hy
  dsimp
  unfold Mmul edgeFactor
  change (∑ j : Fin 2, Model.M .hardcore a (0 : Fin 2) j * x j) = _ ∧
    (∑ j : Fin 2, Model.M .hardcore a (1 : Fin 2) j * x j) = _ ∧
    (∑ i : Fin 2, ∑ j : Fin 2, x i * Model.M .hardcore a i j * y j) = _
  simp only [Fin.sum_univ_two, Model.M, pi0, pi1, Model.P]
  simp only [Fin.val_zero, Fin.val_one, OfNat.ofNat_ne_one, OfNat.ofNat_ne_zero, true_and,
    false_and, ↓reduceIte]
  norm_num only [Nat.one_ne_zero, Nat.zero_ne_one, false_and, ↓reduceIte]
  simp only [ite_false, ite_true]
  constructor
  · field_simp
    <;> nlinarith
  constructor
  · field_simp
    <;> nlinarith
  have hx0 : x 0 = 1 - x 1 := by linarith
  have hy0 : y 0 = 1 - y 1 := by linarith
  rw [hx0, hy0]
  field_simp
  <;> ring
