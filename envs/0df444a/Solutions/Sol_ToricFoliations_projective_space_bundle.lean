-- Prove2me | solution 1 for ToricFoliations.projective_space_bundle
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T14:26:02.118346+00:00
-- url     : https://prove2.me/submissions/29a9d02f-6d3e-4478-bcd4-003cbdbbd680

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
theorem solution : ¬ (∀ {n r : ℕ} (hr : r ≤ n) (R : ExtremalRay n)
    (hExt : R.isExtremal) (C : WallData n) (hC : C ∈ R.curves)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < rayLength R V),
    IsProjectiveSpaceBundle hr C ∧ curveLength C V = r + 1) := by
  intro h
  have := (h (n := 1) (r := 0) (Nat.zero_le 1) S216TFD.R trivial S216TFD.W
    (Finset.mem_singleton_self _) ⊥ (by simp) (by rw [S216TFD.ray_eq]; norm_num)).2
  rw [S216TFD.length_eq] at this
  norm_num at this
