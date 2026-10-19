-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalCanonicalAcceptedCoefficient_sourceScale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/73f0fd39-20f3-4f2a-9767-0504580ad4db

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (ξ : BipartiteUnitVector d) (i : Fin d) :
    Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) =
      dSVDensityRationalCanonicalAcceptedCoefficient w N ξ i := by
  have d_nonzero : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt dimension)
  have n_nonzero : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt grid)
  have source_positive :
      0 < ‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖ := by
    have source_sq := dSVUniformDensityThresholdRaw_norm_sq N d
    have product_positive : (0 : ℝ) < (d : ℝ) * (N : ℝ) := by
      positivity
    nlinarith [norm_nonneg
      (sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ)))]
  have left_nonnegative :
      0 ≤ Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) := by
    positivity
  have right_nonnegative :=
    dSVDensityRationalCanonicalAcceptedCoefficient_nonneg
      w N ξ i
  have same_square :
      (Real.sqrt (w * (d : ℝ)) *
        (‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) *
        Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ)) ^ 2 =
        dSVDensityRationalCanonicalAcceptedCoefficient
          w N ξ i ^ 2 := by
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ w * (d : ℝ)),
      inv_pow, dSVUniformDensityThresholdRaw_norm_sq,
      Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤
          (dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val),
      dSVDensityRationalPhysicalAcceptedRank_targetCoefficient_sq
        width N ξ i]
    field_simp
  nlinarith
end QuantumParallelRepetition
