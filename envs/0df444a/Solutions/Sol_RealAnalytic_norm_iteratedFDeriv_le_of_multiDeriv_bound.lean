-- Prove2me | solution 1 for RealAnalytic.norm_iteratedFDeriv_le_of_multiDeriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T20:27:11.320116+00:00
-- url     : https://prove2.me/submissions/8ffd889a-6e42-470e-980a-dcc7eb7bbcc3

import Theorems.Thm_ContinuousMultilinearMap_norm_le_of_coordinate_bound
import Theorems.Thm_HunterPDE_Shared_iteratedFDeriv_apply_coordinates_eq_multiDeriv
import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Positivity

open scoped ContDiff
open HunterPDE.Shared
set_option autoImplicit false

theorem list_count_perm {n : ℕ} (l : List (Fin n)) :
    l.Perm (multiIndexList (fun i => l.count i)) := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  rw [multiIndexList, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

theorem solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {s : Set (EuclideanSpace ℝ (Fin n))}
    (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ s) {k : ℕ} (hk : 1 ≤ k)
    {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ α : Fin n → ℕ, ∑ i, α i = k → |multiDeriv u α y| ≤ M) :
    ‖iteratedFDeriv ℝ k u y‖ ≤ (n + 1 : ℝ) ^ k * M := by
  have hbound : ‖iteratedFDeriv ℝ k u y‖ ≤ (n : ℝ)^k * M := by
    apply ContinuousMultilinearMap.norm_le_of_coordinate_bound _ hM
    intro a
    rw [HunterPDE.Shared.iteratedFDeriv_apply_coordinates_eq_multiDeriv hs hu hy a, Real.norm_eq_abs]
    apply hb
    have hp := (list_count_perm (List.ofFn a)).length_eq
    rw [multiIndexList, List.length_flatMap] at hp
    simp only [List.length_replicate] at hp
    rw [← List.ofFn_eq_map, List.sum_ofFn] at hp
    simpa using hp.symm
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (by simp) k) hM)
