-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalProjectiveThresholdBin_eq_true_iff_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/50ac5c34-d84c-489a-886f-0115918322d7

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalAcceptedRank_eq_floor

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ} (width : 0 < w) (grid : 0 < N)
    (ξ : BipartiteUnitVector d)
    (i : Fin d) (k : Fin N) :
    dSVDensityRationalProjectiveThresholdBin w N k
        ((dSVSoftBobLeftReducedDensity_posSemidef
          ξ).isHermitian.eigenvalues i) = true ↔
      k.val <
        (dSVDensityRationalPhysicalAcceptedRank w N ξ i).val := by
  have real_grid : (0 : ℝ) < N := by exact_mod_cast grid
  have pass_nonnegative :=
    (dSVRationalSoftPass_mem_unit width
      ((dSVSoftBobLeftReducedDensity_posSemidef
        ξ).eigenvalues_nonneg i)).1
  have product_nonnegative :
      0 ≤ dSVRationalSoftPass w
          ((dSVSoftBobLeftReducedDensity_posSemidef
            ξ).isHermitian.eigenvalues i) * (N : ℝ) :=
    mul_nonneg pass_nonnegative real_grid.le
  rw [dSVDensityRationalPhysicalAcceptedRank_eq_floor
    width grid ξ i]
  unfold dSVDensityRationalProjectiveThresholdBin
  simp only [decide_eq_true_eq]
  rw [dSVUniformDensityThresholdGrid_apply grid,
    div_le_iff₀ real_grid]
  constructor
  · intro accepted
    have cast :
        ((k.val + 1 : ℕ) : ℝ) ≤
          dSVRationalSoftPass w
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) * (N : ℝ) := by
      simpa using accepted
    have below := (Nat.le_floor_iff product_nonnegative).2 cast
    omega
  · intro below
    have integer :
        k.val + 1 ≤
          Nat.floor
            (dSVRationalSoftPass w
              ((dSVSoftBobLeftReducedDensity_posSemidef
                ξ).isHermitian.eigenvalues i) * (N : ℝ)) := by
      omega
    have cast := (Nat.le_floor_iff product_nonnegative).1 integer
    simpa using cast
end QuantumParallelRepetition
