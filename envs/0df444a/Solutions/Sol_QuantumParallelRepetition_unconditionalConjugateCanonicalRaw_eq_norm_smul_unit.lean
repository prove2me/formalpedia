-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/292fa96d-00aa-4195-92a4-acb99e1d1af0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalCanonicalRaw_eq_norm_smul_unit

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
    unconditionalConjugatePureVector
        (dSVDensityRationalCanonicalAcceptedTarget
          w N gamma) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val := by
  have raw := unconditionalCanonicalRaw_eq_norm_smul_unit
    width grid fine gamma
  ext i
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z i) raw
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star
          ((dSVDensityRationalCanonicalAcceptedUnitTarget
            width grid fine gamma).val i)
  change
    dSVDensityRationalCanonicalAcceptedTarget
      w N gamma i =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        (dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val i at coefficient
  rw [coefficient]
  simp
end QuantumParallelRepetition
