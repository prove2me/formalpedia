-- Prove2me | solution 1 for ToricFoliations.length_bound
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:25:53.277768+00:00
-- url     : https://prove2.me/submissions/54df18cd-befd-432b-b56f-7598ea9f20b6

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

/-- An extremal ray consisting of the single degenerate curve. -/
def R : ExtremalRay 1 where
  curves := {W}
  nonempty := Finset.singleton_nonempty W
  isExtremal := True

lemma length_eq : curveLength W (⊥ : Submodule ℂ (Complexified 1)) = 2 := by
  unfold curveLength
  simp only [W, toComplex_zero, Submodule.zero_mem, if_true]
  unfold divisorIntersection
  simp [lastIndex, wallIndex, W]
  norm_num

lemma ray_eq : rayLength R (⊥ : Submodule ℂ (Complexified 1)) = 2 := by
  unfold rayLength
  simp [R, length_eq]

end S216TFD

open ToricFoliations in
theorem solution : ¬ (∀ {n r : ℕ} (R : ExtremalRay n) (hExt : R.isExtremal)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r),
    rayLength R V ≤ r + 1) := by
  intro h
  have := h (n := 1) (r := 0) S216TFD.R trivial ⊥ (by simp)
  rw [S216TFD.ray_eq] at this
  norm_num at this
