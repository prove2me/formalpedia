-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateCanonicalAcceptedTarget_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/07589c8c-473d-4cf5-890b-d5d3218582ad

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalCanonicalAcceptedCoefficient_sourceScale
import Theorems.Thm_QuantumParallelRepetition_unconditionalRationalMixedConjugateBobSpectral_sum
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateCanonicalAcceptedTarget_apply

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
    (ξ ζ : BipartiteUnitVector d)
    (a b : Fin d) :
    (∑ i : Fin d, ∑ j : Fin d,
      (Real.sqrt (w * (d : ℝ)) : ℂ) *
        ((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        (Real.sqrt
          ((dSVDensityRationalPhysicalAcceptedRank
            w N ξ i).val : ℝ) : ℂ) *
        star
          ((dSVDensityRationalCanonicalAliceBasis ξ :
            Matrix (Fin d) (Fin d) ℂ) a i) *
        dSVDensityRationalLocalSpectralPairBasisOverlap
          ξ ζ i j *
        star
          ((dSVUniformDensityThresholdLeftBobBasis ζ :
            Matrix (Fin d) (Fin d) ℂ) b j)) =
      star
        (dSVDensityRationalCanonicalAcceptedTarget
          w N ξ (a, b)) := by
  classical
  calc
    _ =
        ∑ i : Fin d,
          ((Real.sqrt (w * (d : ℝ)) : ℂ) *
            ((‖sharedThresholdResourceRaw (d := Fin d)
              (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
            (Real.sqrt
              ((dSVDensityRationalPhysicalAcceptedRank
                w N ξ i).val : ℝ) : ℂ) *
            star
              ((dSVDensityRationalCanonicalAliceBasis ξ :
                Matrix (Fin d) (Fin d) ℂ) a i)) *
          (∑ j : Fin d,
            dSVDensityRationalLocalSpectralPairBasisOverlap
              ξ ζ i j *
            star
              ((dSVUniformDensityThresholdLeftBobBasis ζ :
                Matrix (Fin d) (Fin d) ℂ) b j)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ =
        ∑ i : Fin d,
          (dSVDensityRationalCanonicalAcceptedCoefficient
            w N ξ i : ℂ) *
          star
            ((dSVDensityRationalCanonicalAliceBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) a i) *
          star
            ((dSVUniformDensityThresholdLeftBobBasis ξ :
              Matrix (Fin d) (Fin d) ℂ) b i) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [unconditionalRationalMixedConjugateBobSpectral_sum]
          have coefficient := congrArg (fun x : ℝ => (x : ℂ))
            (unconditionalCanonicalAcceptedCoefficient_sourceScale
              width grid dimension ξ i)
          push_cast at coefficient
          rw [← coefficient]
          push_cast
          ring
    _ = _ :=
      (unconditionalConjugateCanonicalAcceptedTarget_apply
        w ξ a b).symm
end QuantumParallelRepetition
