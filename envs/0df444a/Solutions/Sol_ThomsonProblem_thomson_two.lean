-- Prove2me | solution 1 for ThomsonProblem.thomson_two
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T04:46:27.61497+00:00
-- url     : https://prove2.me/submissions/f1fd1f2a-0bca-42ae-98b6-f82322bcb75b

import Mathlib
import Definitions.Def_ThomsonProblem_defs

open ThomsonProblem in
lemma energy_two_d562c69e (x : Fin 2 → Space) :
    coulombEnergy x = 1 / dist (x 0) (x 1) := by
  have h0 : Finset.Ioi (0 : Fin 2) = {1} := by decide
  have h1 : Finset.Ioi (1 : Fin 2) = ∅ := by decide
  simp [coulombEnergy, Fin.sum_univ_two, h0, h1]

open ThomsonProblem in
lemma antipodal_dist_d562c69e : dist (antipodalPair 0) (antipodalPair 1) = 2 := by
  rw [EuclideanSpace.dist_eq]
  simp [antipodalPair, Fin.sum_univ_three, Real.dist_eq]
  norm_num

open ThomsonProblem in
lemma antipodal_norm_d562c69e (i : Fin 2) : ‖antipodalPair i‖ = 1 := by
  fin_cases i <;> simp [antipodalPair, EuclideanSpace.norm_eq, Fin.sum_univ_three]

open ThomsonProblem in
theorem solution :
    IsEnergyMinimizer antipodalPair ∧ coulombEnergy antipodalPair = 1 / 2 := by
  have hE : coulombEnergy antipodalPair = 1 / 2 := by
    rw [energy_two_d562c69e, antipodal_dist_d562c69e]
  refine ⟨⟨⟨antipodal_norm_d562c69e, ?_⟩, fun y hy => ?_⟩, hE⟩
  · intro a b hab
    have hne : antipodalPair 0 ≠ antipodalPair 1 := by
      intro h
      have := antipodal_dist_d562c69e
      rw [h, dist_self] at this
      norm_num at this
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hne
    · exact absurd hab.symm hne
    · rfl
  · rw [hE, energy_two_d562c69e]
    obtain ⟨hn, hinj⟩ := hy
    have hne : y 0 ≠ y 1 := fun h => absurd (hinj h) (by decide)
    have hpos : 0 < dist (y 0) (y 1) := dist_pos.mpr hne
    have hle : dist (y 0) (y 1) ≤ 2 := by
      have := dist_le_norm_add_norm (y 0) (y 1)
      rw [hn 0, hn 1] at this
      linarith
    exact one_div_le_one_div_of_le hpos hle
