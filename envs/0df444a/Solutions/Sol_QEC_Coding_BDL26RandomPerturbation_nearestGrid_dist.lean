-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.nearestGrid_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:56:29.609199+00:00
-- url     : https://prove2.me/submissions/27458234-28bf-40a7-8738-332866d20bb8

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Int.Interval
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GridCover
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (K : ℕ) (p : Space) (hp : ‖p‖ ≤ K) :
    dist p (gridPoint K (nearestGrid K p hp)) ≤ 1 := by
  have hcoord (i : Fin 3) : (p i - (round (p i) : ℝ))^2 ≤ (1/2 : ℝ)^2 := by
    have h := mul_self_le_mul_self (abs_nonneg (p i - (round (p i) : ℝ)))
      (abs_sub_round (p i))
    simpa only [← pow_two, sq_abs] using h
  have hsq : ‖p-gridPoint K (nearestGrid K p hp)‖^2 ≤ (3 : ℝ)/4 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i : Fin 3, (p i - (round (p i) : ℝ))^2) ≤ 3/4
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have h0 := hcoord 0
    have h1 := hcoord 1
    have h2 := hcoord 2
    norm_num at h0 h1 h2 ⊢
    linarith
  rw [dist_eq_norm]
  have hn := norm_nonneg (p-gridPoint K (nearestGrid K p hp))
  nlinarith
end QEC.Coding.BDL26RandomPerturbation
