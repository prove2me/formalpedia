-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalCanonicalRaw_eq_norm_smul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/b0526781-48a8-4245-a3a2-b9807a00e5b9

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
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalCanonicalAcceptedTarget w N gamma =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val := by
  exact (NormedSpace.norm_smul_normalize
    (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma)).symm
end QuantumParallelRepetition
