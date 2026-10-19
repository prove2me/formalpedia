-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalCanonicalAcceptedScale_sq_eq_diagonalBorn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/5e4f34ec-964e-404a-bd09-b07a0966efb5

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {d N : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N) (dimension : 0 < d)
    (gamma : BipartiteUnitVector d) :
    (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ / Real.sqrt (w * (d : ℝ))) ^ 2 =
      dSVDensityRationalPhysicalDiagonalBornSuccess
        grid dimension w gamma := by
  have dimension_real : 0 < (d : ℝ) := by
    exact_mod_cast dimension
  rw [div_pow,
    dSVDensityRationalCanonicalAcceptedTarget_norm_sq
      width N gamma,
    Real.sq_sqrt (by positivity : 0 ≤ w * (d : ℝ)),
    dSVDensityRationalPhysicalDiagonalBornSuccess_eq]
  field_simp [ne_of_gt width, ne_of_gt dimension_real]
end QuantumParallelRepetition
