-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalRationalMixedConjugateBobSpectral_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/abad776f-1944-416b-b52f-ada297093a40

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateBobBasisOverlap_sum

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
    {d : ℕ} (ξ ζ : BipartiteUnitVector d)
    (i b : Fin d) :
    (∑ j : Fin d,
      dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        ((dSVUniformDensityThresholdLeftBobBasis ξ :
          Matrix (Fin d) (Fin d) ℂ) b i) := by
  exact unconditionalConjugateBobBasisOverlap_sum
    (dSVUniformDensityThresholdLeftBobBasis ξ)
    (dSVUniformDensityThresholdLeftBobBasis ζ) i b
end QuantumParallelRepetition
