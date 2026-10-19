-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/97afd649-d992-493d-a7da-8478e2d91b97

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalRawSource_apply
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalSpectralOutcome_eq

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
    {d N n : ℕ} {w : ℝ}
    (width : 0 < w) (grid : 0 < N)
    (ξ ζ : BipartiteUnitVector d)
    (i j : Fin d) (k l : Fin N) (a b : Fin n) :
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState
        (N := N) w n ξ ζ
        (⟨i, finProdFinEquiv (k, a)⟩,
          ⟨j, finProdFinEquiv (l, b)⟩) =
      dSVDensityRationalCanonicalPrefixSpectralOutcome
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩) *
        embezzlementState n (a, b) := by
  classical
  rw [dSVDensityRationalMixedCanonicalSpectralOutcome_eq]
  simp only [
    dSVDensityRationalMixedCanonicalPrefixPhysicalAcceptedSigmaState,
    dSVUniformDensityCorrectedMatchedSigmaWeightedResidual,
    dSVDensityRationalLocalSpectralPairHistory,
    dSVDensityRationalMixedCanonicalPrefixPureHarmonicTensor,
    dSVDensityRationalPhysicalMixedAcceptedPrefixWork,
    dSVCanonicalFailurePrefix,
    Equiv.symm_apply_apply]
  change
    (((‖sharedThresholdResourceRaw (d := Fin d)
        (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
      dSVDensityRationalLocalSpectralPairBasisOverlap ξ ζ i j) *
      ((if k = l ∧
          k.val <
            (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
              w N ξ ζ i j).val
        then (1 : ℂ) else 0) *
        embezzlementState n (a, b)) =
      (((‖sharedThresholdResourceRaw (d := Fin d)
          (fun _ : Fin N => (1 : ℝ))‖⁻¹ : ℝ) : ℂ) *
        dSVDensityRationalMixedCanonicalRawSource
          w N ξ ζ (⟨k, i⟩, ⟨l, j⟩)) *
        embezzlementState n (a, b)
  rw [dSVDensityRationalMixedCanonicalRawSource_apply]
  by_cases same : k = l
  · subst l
    have accepted :=
      dSVDensityRationalPhysicalMixedAcceptedThreshold_iff
        width grid ξ ζ i j k
    by_cases below : k.val <
        (dSVDensityRationalPhysicalMixedAcceptedIntersectionRank
          w N ξ ζ i j).val
    · have both := accepted.mpr below
      simp [below, both.1, both.2, mul_assoc]
    · have not_both :
        ¬ (dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ξ).isHermitian.eigenvalues i) = true ∧
          dSVDensityRationalProjectiveThresholdBin w N k
            ((dSVSoftBobLeftReducedDensity_posSemidef
              ζ).isHermitian.eigenvalues j) = true) :=
        fun both => below (accepted.mp both)
      simp [below, not_both]
  · simp [same]
end QuantumParallelRepetition
