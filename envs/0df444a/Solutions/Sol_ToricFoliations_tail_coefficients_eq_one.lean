-- Prove2me | solution 1 for ToricFoliations.tail_coefficients_eq_one
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:25:08.074398+00:00
-- url     : https://prove2.me/submissions/c7e5639a-a370-4a9f-959e-f7572490e2cb

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace S216TFD
open ToricFoliations

/-- Degenerate wall data: n = 1, all vectors zero, a = (1, 2), all multiplicities 1. -/
def W : WallData 1 where
  hn := Nat.one_pos
  v := fun _ => 0
  a := ![1, 2]
  relation := by simp
  an_pos := by simp [wallIndex]
  aLast_pos := by simp [lastIndex]
  sorted := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  mWall := 1
  mSigma := 1
  mSigma' := 1
  mWall_pos := Nat.one_pos
  mSigma_pos := Nat.one_pos
  mSigma'_pos := Nat.one_pos
  wall_dvd_sigma := dvd_refl 1
  wall_dvd_sigma' := dvd_refl 1
  gcd_one := ⟨![1, 0], by simp [Fin.sum_univ_two]⟩

lemma toComplex_zero : toComplex (0 : Lattice 1) = 0 := by
  funext i; simp [toComplex]

lemma length_pos : (0 : ℕ) < curveLength W (⊥ : Submodule ℂ (Complexified 1)) := by
  unfold curveLength
  simp only [W, toComplex_zero, Submodule.zero_mem, if_true, Fin.sum_univ_two]
  unfold divisorIntersection
  simp [lastIndex, wallIndex, W]

end S216TFD

open ToricFoliations in
theorem solution : ¬ (∀ {n r : ℕ} (hr : r ≤ n) (C : WallData n)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < curveLength C V)
    (htail : ∀ j : Fin (r + 1), toComplex (C.v (tailIndex hr j)) ∈ V),
    ∀ j : Fin (r + 1), C.a (tailIndex hr j) = 1) := by
  intro h
  have := h (n := 1) (r := 0) (Nat.zero_le 1) S216TFD.W ⊥ (by simp) S216TFD.length_pos
    (fun j => by simp [S216TFD.W, S216TFD.toComplex_zero]) 0
  simp [S216TFD.W, tailIndex] at this
