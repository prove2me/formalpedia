-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalPhaseCanonicalRaw_eq_norm_smul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/7e48ba9d-c946-422b-9e7e-f7e2f53ed042

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateCanonicalRaw_eq_norm_smul_unit

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
    {d N B m : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (fine : (d : ℝ) / (N : ℝ) < 1 / (w + 1))
    (gamma : BipartiteUnitVector d) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B
        (unconditionalConjugatePureVector
          (dSVDensityRationalCanonicalAcceptedTarget
            w N gamma))
        (fun _ _ _ => embezzlementState m) =
      ‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ •
        dSVDensityRationalPublicBucketCoherentPhaseSigmaState
          B
          (unconditionalConjugatePureVector
            (dSVDensityRationalCanonicalAcceptedUnitTarget
              width grid fine gamma).val)
          (fun _ _ _ => embezzlementState m) := by
  have raw :=
    unconditionalConjugateCanonicalRaw_eq_norm_smul_unit
      width grid fine gamma
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  have coefficient := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) => z (i, j)) raw
  change
    (ePRState B (φ, ψ) *
      star (dSVDensityRationalCanonicalAcceptedTarget
        w N gamma (i, j))) *
      embezzlementState m (a, b) =
    (‖dSVDensityRationalCanonicalAcceptedTarget
      w N gamma‖ : ℂ) *
      ((ePRState B (φ, ψ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j))) *
        embezzlementState m (a, b))
  change
    star (dSVDensityRationalCanonicalAcceptedTarget
      w N gamma (i, j)) =
      (‖dSVDensityRationalCanonicalAcceptedTarget
        w N gamma‖ : ℂ) *
        star ((dSVDensityRationalCanonicalAcceptedUnitTarget
          width grid fine gamma).val (i, j)) at coefficient
  rw [coefficient]
  ring
end QuantumParallelRepetition
