-- Prove2me | solution 1 for QEC.Locality.daiLiRecursivePotential_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:29:27.597825+00:00
-- url     : https://prove2.me/submissions/bb5dd03d-18d2-477e-82c0-964622672a49

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution {ell : ℝ} {root parent child : Nat}
    (hEll : 0 ≤ ell) (hBalanced : 10 * child ≤ 9 * parent) :
    daiLiRecursivePotential ell root parent + 8 * ell * Real.sqrt parent ≤
      daiLiRecursivePotential ell root child := by
  have hChildBound : (child : ℝ) ≤ (361 : ℝ) / 400 * parent := by
    have hBalancedReal : (10 : ℝ) * child ≤ 9 * parent := by
      exact_mod_cast hBalanced
    nlinarith
  have hChildNonneg : 0 ≤ (child : ℝ) := by positivity
  have hParentNonneg : 0 ≤ (parent : ℝ) := by positivity
  have hScaledNonneg : 0 ≤ (19 : ℝ) / 20 * Real.sqrt parent := by positivity
  have hScaledSq : (((19 : ℝ) / 20 * Real.sqrt parent) ^ 2) =
      (361 : ℝ) / 400 * parent := by
    rw [mul_pow, Real.sq_sqrt hParentNonneg]
    ring
  have hSqrtChild : Real.sqrt child ≤ (19 : ℝ) / 20 * Real.sqrt parent := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) hScaledNonneg).mp
    rw [Real.sq_sqrt hChildNonneg, hScaledSq]
    exact hChildBound
  unfold daiLiRecursivePotential
  nlinarith
end QEC.Locality
