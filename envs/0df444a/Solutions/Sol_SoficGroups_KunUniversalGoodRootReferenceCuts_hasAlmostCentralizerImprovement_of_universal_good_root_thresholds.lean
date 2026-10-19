-- Prove2me | solution 1 for SoficGroups.KunUniversalGoodRootReferenceCuts.hasAlmostCentralizerImprovement_of_universal_good_root_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/e7012101-4719-414a-9ce8-de498b8f1b6d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationGraph_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_hasAlmostCentralizerImprovement_of_rooted_reference_cuts
import Theorems.Thm_SoficGroups_KunUniversalGoodRootReferenceCuts_reference_difference_le_of_good_root_threshold
noncomputable section
namespace SoficGroups
section
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace LocalMultiplicativeOn
variable {G : Type u} {H : Type v} [Group G] [Group H]
end LocalMultiplicativeOn
namespace MatrixCorner
variable {ι A : Type*} [Fintype ι] [Ring A]
end MatrixCorner
section NoncommutativeElementaryGroup
variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Ring R]
end NoncommutativeElementaryGroup
section FiniteGeneration
variable {R : Type*} [Ring R]
variable [Algebra (ZMod 2) R]
end FiniteGeneration
namespace SourceGeneration
open scoped commutatorElement
end SourceGeneration
namespace PrefixCompressionU
open scoped BigOperators
end PrefixCompressionU
namespace PrefixCompression
open scoped BigOperators
end PrefixCompression
namespace CheegerPoincare
open scoped BigOperators
end CheegerPoincare
namespace ThompsonPrefixLocal
open scoped BigOperators
end ThompsonPrefixLocal
namespace ComponentMidrankVariance
open scoped BigOperators
end ComponentMidrankVariance
namespace ThompsonPrefixInsertion
open scoped BigOperators
end ThompsonPrefixInsertion
namespace MidrankPermutationEnergy
end MidrankPermutationEnergy
namespace RankArcCharging
open scoped BigOperators
end RankArcCharging
namespace ExceptionalRankOffset
open Filter Topology
open scoped BigOperators
end ExceptionalRankOffset
namespace ThompsonPrefixInsertion
end ThompsonPrefixInsertion
universe u₁ u₂ u₃
section ElementaryRingQuotient
variable {ι : Type u₁} {R : Type u₂} {S : Type u₃}
  [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]
end ElementaryRingQuotient
namespace CompressionCriterion
open Filter Topology
end CompressionCriterion
namespace ThompsonPrefixInsertion
open scoped commutatorElement
end ThompsonPrefixInsertion
namespace LeavittElementaryMorita
open scoped BigOperators commutatorElement
section ElementaryBlockFlattening
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]
end ElementaryBlockFlattening
section ElementaryReindexing
variable {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Ring R]
end ElementaryReindexing
section ElementaryCoefficientEquivalence
variable {ι R S : Type*} [Fintype ι] [DecidableEq ι]
  [Ring R] [Ring S]
end ElementaryCoefficientEquivalence
end LeavittElementaryMorita
namespace ThompsonFiniteGeneration
open ThompsonPrefixInsertion
end ThompsonFiniteGeneration
end
section
open Filter Topology
section ThreeProjectionSumOfSquares
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end ThreeProjectionSumOfSquares
section TwoOrthogonalSectors
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end TwoOrthogonalSectors
section ThreeOrthogonalProjections
variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]
variable (V : Fin 3 → Submodule ℂ H)
  [∀ i, (V i).HasOrthogonalProjection]
end ThreeOrthogonalProjections
section ThreeFiniteUnitaryFixedSpaces
universe u₂ v₂
end ThreeFiniteUnitaryFixedSpaces
end
namespace ErshovJaikinFiniteSpectral
open Filter Topology
universe u v
section FiniteUnitaryAveraging
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end FiniteUnitaryAveraging
end ErshovJaikinFiniteSpectral
section
open scoped BigOperators commutatorElement
section ActualBlockRoots
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
end ActualBlockRoots
universe u₁ v₁
section FiniteSubgroupAveraging
variable {G : Type*} {H : Type*} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end FiniteSubgroupAveraging
end
section
open scoped BigOperators commutatorElement
universe u
section BinaryCoefficientSpan
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
end BinaryCoefficientSpan
section FiniteBlockRoots
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
end FiniteBlockRoots
end
section
open scoped BigOperators
universe vSharp
end
section
open scoped BigOperators
end
namespace KunThomFiberCoarea
end KunThomFiberCoarea
namespace KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
end KunRootedIndicatorCrossing
namespace KunThomInvariantOrthogonal
section
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end
section
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
end
end KunThomInvariantOrthogonal
namespace KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
end KunRootedWordPower
namespace KunActualSoficRootRadius
open Filter Topology
open scoped BigOperators Pointwise
end KunActualSoficRootRadius
namespace KunDirectedIndicatorJensen
open scoped BigOperators
end KunDirectedIndicatorJensen
namespace KunFinitePermutationMarkovMass
open scoped BigOperators
end KunFinitePermutationMarkovMass
namespace KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff
end KunResidualExpanderDecomposition
namespace KunDiagonalGoodRootGraphLoss
open scoped BigOperators symmDiff
end KunDiagonalGoodRootGraphLoss
namespace KunCompletedPrunedComponent
open scoped BigOperators
end KunCompletedPrunedComponent
namespace MatchedComponentCompletion
open scoped BigOperators
end MatchedComponentCompletion
namespace MatchedComponentExitBudget
open Filter Topology
open scoped BigOperators
end MatchedComponentExitBudget
namespace KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
end KunRealComplexMarkovBridge
namespace KunRootedWordPower
section
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v
end
section
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u
end
end KunRootedWordPower
namespace KunActualRootedModelBridge
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators
universe u
end KunActualRootedModelBridge
namespace KunSharpThresholdCut
open MeasureTheory Set
open scoped BigOperators ENNReal symmDiff
end KunSharpThresholdCut
namespace KunActualFinalRestrictedVariation
open scoped BigOperators
end KunActualFinalRestrictedVariation
namespace MatchedFirstStageWordRadiusTransfer
open Filter Topology
open scoped BigOperators
end MatchedFirstStageWordRadiusTransfer
namespace SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
end SourceCompressionMatching
namespace SourceCompressionTransportCrossing
open Filter Topology
open scoped BigOperators
end SourceCompressionTransportCrossing
namespace KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
end KunResidualRetainedSelection
namespace KunUniversalGoodRootReferenceCuts
open scoped symmDiff
private theorem rooted_reference_cut_bounds_of_slow_tolerance
    {h d C t N Δ u e : ℝ}
    (hh : 0 < h) (hd : 0 ≤ d) (hC : 0 ≤ C)
    (ht : 0 ≤ t) (hN : 0 < N)
    (hdifference : Δ ≤ C * t)
    (hcard : u ≤ N + Δ)
    (hboundary : e ≤ (h * t / (2 * (h + 8 * d) * N)) * u)
    (hslow : 5 * (4 + h * C) * t ≤ h * N) :
    2 * Δ ≤ N ∧
      (h + 8 * d) * e ≤ h * t ∧
      5 * (4 * e + h * Δ) ≤ h * N := by
  have hden : 0 < h + 8 * d := by nlinarith
  have hCt : 5 * (C * t) ≤ N := by
    have hscaled : h * (5 * (C * t)) ≤ h * N := by
      nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) ht]
    exact le_of_mul_le_mul_left hscaled hh
  have hCtzero : 0 ≤ C * t := mul_nonneg hC ht
  have hnear : 2 * Δ ≤ N := by nlinarith
  have hu : u ≤ 2 * N := by nlinarith
  have hcoefficient : 0 ≤ h * t / (2 * (h + 8 * d) * N) := by
    positivity
  have he : e ≤ h * t / (h + 8 * d) := by
    calc
      e ≤ (h * t / (2 * (h + 8 * d) * N)) * u := hboundary
      _ ≤ (h * t / (2 * (h + 8 * d) * N)) * (2 * N) :=
        mul_le_mul_of_nonneg_left hu hcoefficient
      _ = h * t / (h + 8 * d) := by field_simp
  have himprovement : (h + 8 * d) * e ≤ h * t := by
    have he' := (le_div_iff₀ hden).mp he
    nlinarith
  have het : e ≤ t := by
    calc
      e ≤ h * t / (h + 8 * d) := he
      _ ≤ t := (div_le_iff₀ hden).2 (by nlinarith)
  refine ⟨hnear, himprovement, ?_⟩
  calc
    5 * (4 * e + h * Δ) ≤ 5 * (4 * t + h * (C * t)) := by
      gcongr
    _ = 5 * (4 + h * C) * t := by ring
    _ ≤ h * N := hslow
end KunUniversalGoodRootReferenceCuts
namespace KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise symmDiff
universe u
end KunRootedWordPower
namespace SourceCompressionRetainedDiscard
open Filter Topology
open scoped BigOperators symmDiff
end SourceCompressionRetainedDiscard
namespace SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators
end SourceGeneratedWordCrossing
namespace KunRootedUniversalToleranceNumerics
end KunRootedUniversalToleranceNumerics
namespace SourceBothCompressionNormalization
end SourceBothCompressionNormalization
namespace KunCompletedProductDiagonalSparseCut
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
end KunCompletedProductDiagonalSparseCut
namespace KunTransportedAmbientOverlap
open Filter Topology
open scoped BigOperators symmDiff
end KunTransportedAmbientOverlap
namespace KunUniformCompletedRootRadiusImprovement
open SoficGroups.KunDiagonalGoodRootGraphLoss
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
universe u
end KunUniformCompletedRootRadiusImprovement
namespace CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
end CompletedChosenWordLocalRoot
namespace CompletedSourceChosenWordRestrictionTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open scoped BigOperators
end CompletedSourceChosenWordRestrictionTransfer
namespace CompletedSourceFinalGeneratorTransfer
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CompletedSourceChosenWordRestrictionTransfer
end CompletedSourceFinalGeneratorTransfer
namespace CompletedPrescribedSpectralRadiusSchedule
open Filter Topology
open scoped Pointwise
end CompletedPrescribedSpectralRadiusSchedule
namespace KunSourceUnconditionalFullDecomposition
section
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunActualRootedModelBridge
open SoficGroups.KunRootedWordPower
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators symmDiff
end
section
open Filter Topology
end
end KunSourceUnconditionalFullDecomposition
namespace KunActualCompressedSourceGroupFoundations
universe v
end KunActualCompressedSourceGroupFoundations
namespace KunExactKazhdanGeneratorChange
universe u v
end KunExactKazhdanGeneratorChange
namespace KunExactActualSourceAmbientGenerators
section
open SoficGroups.KunExactKazhdanGeneratorChange
end
section
end
end KunExactActualSourceAmbientGenerators
namespace KunUnconditionalActualSourceGeneratorData
open SoficGroups.KunExactKazhdanGeneratorChange
open SoficGroups.KunExactActualSourceAmbientGenerators
end KunUnconditionalActualSourceGeneratorData
namespace SourceCommonComponentComparisonBad
open Filter Topology
open scoped BigOperators
end SourceCommonComponentComparisonBad
namespace SourceCommonOffsetMidrankEnergy
open Filter Topology
open scoped BigOperators
end SourceCommonOffsetMidrankEnergy
namespace SourceCommonComponentRankNoBad
open Filter Topology
open scoped BigOperators
end SourceCommonComponentRankNoBad
namespace KunPositiveWordMidrankEnergy
open Filter Topology
open scoped BigOperators
end KunPositiveWordMidrankEnergy
namespace KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
end KunAdditiveMedianPoincare
namespace KunCompletedComponentMidrankVariation
open Filter Topology
open scoped BigOperators
end KunCompletedComponentMidrankVariation
namespace KunGlobalActualAdditiveMidrankVariance
open Filter Topology
open scoped BigOperators
end KunGlobalActualAdditiveMidrankVariance
namespace KunCommonRankArcInvariance
open Filter Topology
open scoped BigOperators
end KunCommonRankArcInvariance
namespace ChosenCayleyMatchedComponentRealization
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.KunResidualRetainedSelection
open scoped BigOperators Pointwise symmDiff
end ChosenCayleyMatchedComponentRealization
namespace CanonicalProductRadiusBadMatchedCapture
open Filter Topology
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.ChosenCayleyMatchedComponentRealization
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open scoped BigOperators Pointwise symmDiff
end CanonicalProductRadiusBadMatchedCapture
namespace CompletedSelectedCentralizerPairwiseSource
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedFirstStageWordRadiusTransfer
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
end CompletedSelectedCentralizerPairwiseSource
namespace KunActualSelectedCentralizerFiniteModel
open Filter Topology
end KunActualSelectedCentralizerFiniteModel
namespace SourceTopLevelCompression
open Filter
end SourceTopLevelCompression
namespace ThompsonFFiniteQuotient
variable {G : Type*} [Group G]
end ThompsonFFiniteQuotient
namespace ThompsonFTwoRelatorLEF
open scoped commutatorElement
end ThompsonFTwoRelatorLEF
namespace ThompsonFLocalWitness
open ThompsonPrefixInsertion
end ThompsonFLocalWitness
section
end
namespace KunUnconditionalActualSourceDecomposition
open Filter Topology
open SoficGroups.KunSourceUnconditionalFullDecomposition
open SoficGroups.KunExactActualSourceAmbientGenerators
open SoficGroups.KunUnconditionalActualSourceGeneratorData
end KunUnconditionalActualSourceDecomposition
namespace KunCombinedPrescribedRootSourceTolerance
open Filter Topology
end KunCombinedPrescribedRootSourceTolerance
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
end KunLiteralSourceSelectedComponents
namespace KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators
end KunActualBothTransportedOverlapScales
namespace SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v
end SourceProductThroughAlpha
namespace SourceRetainedActualMatching
open Filter Topology
open scoped BigOperators symmDiff
end SourceRetainedActualMatching
namespace KunActualBothTransportedOverlapScales
open Filter Topology
open scoped BigOperators
end KunActualBothTransportedOverlapScales
namespace KunLiteralNineSourceCompletedCentralizerModels
open Filter Topology
open scoped BigOperators
end KunLiteralNineSourceCompletedCentralizerModels
namespace KunActualFirstStageReferenceExpansion
open Filter Topology
open scoped BigOperators
end KunActualFirstStageReferenceExpansion
namespace SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
end SourceProductThroughAlpha
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators Pointwise
end KunLiteralSourceSelectedComponents
namespace SourceGuardedCanonicalSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
end SourceGuardedCanonicalSelection
namespace KunActualSourceURetainedNoPremise
open Filter Topology
open scoped BigOperators symmDiff
end KunActualSourceURetainedNoPremise
namespace KunLiteralSourceSelectedComponents
open Filter Topology
open scoped BigOperators Pointwise
end KunLiteralSourceSelectedComponents
namespace SourceProductThroughAlpha
open scoped BigOperators
end SourceProductThroughAlpha
namespace KunGuardedCanonicalMatchedDensity
open Filter Topology
end KunGuardedCanonicalMatchedDensity
namespace KunActualCanonicalSelectedPruning
open Filter Topology
open SoficGroups.MatchedComponentCompletion
end KunActualCanonicalSelectedPruning
namespace KunActualCanonicalPrunedSourceBadDensity
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
end KunActualCanonicalPrunedSourceBadDensity
namespace KunActualTwicePrunedFirstFactorRootBad
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.MatchedComponentExitBudget
open SoficGroups.KunActualSoficRootRadius
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open SoficGroups.CompletedSourceFinalGeneratorTransfer
open scoped BigOperators Pointwise
end KunActualTwicePrunedFirstFactorRootBad
namespace KunActualSelectedPrunedSourceFiniteModelBridge
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.KunActualSoficRootRadius
open scoped BigOperators Pointwise
end KunActualSelectedPrunedSourceFiniteModelBridge
namespace KunActualCanonicalSelectedFiniteModelComposition
open Filter Topology
open SoficGroups.MatchedComponentCompletion
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
end KunActualCanonicalSelectedFiniteModelComposition
namespace KunLiteralSourceSelectedComponents
end KunLiteralSourceSelectedComponents
namespace KunActualSourceSelectedCompletedGeneratorExpansion
open Filter Topology
open scoped BigOperators
end KunActualSourceSelectedCompletedGeneratorExpansion
namespace KunLiteralNineSourceFiniteModels
open Filter Topology
open SoficGroups.CanonicalProductRadiusBadMatchedCapture
open scoped BigOperators Pointwise
end KunLiteralNineSourceFiniteModels
namespace SourceTopLevelCompressionFinal
open SoficGroups.SourceTopLevelCompression
open SoficGroups.KunLiteralNineSourceFiniteModels
end SourceTopLevelCompressionFinal
end SoficGroups
end
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunUniversalGoodRootReferenceCuts
open scoped symmDiff
namespace SoficGroups.KunUniversalGoodRootReferenceCuts
theorem _root_.solution
    {V ι : Type*}
    [Fintype V] [Nonempty V] [DecidableEq V]
    [Fintype ι] [Nonempty ι]
    (σ : ι → Equiv.Perm V) (tolerance : ℕ)
    (h q : ℝ) (hpositive : 0 < h) (hq : q < 1)
    (B : Finset V)
    (good : Equiv.Perm V → Finset (V × V))
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (hbad :
      2 * (Fintype.card ι : ℝ) * (B.card : ℝ) ≤
        (tolerance : ℝ))
    (hgood_subset : ∀ p : Equiv.Perm V,
      good p ⊆ SoficGroups.permutationGraph p)
    (hgood_missing : ∀ p : Equiv.Perm V,
      (SoficGroups.permutationGraph p \ good p).card ≤
        2 * B.card)
    (hgood_boundary : ∀ p : Equiv.Perm V,
      SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) (good p) ≤
          SoficGroups.permutationCommutationDefect σ p +
            2 * Fintype.card ι * B.card)
    (hslow :
      5 * (4 + h *
        (216 / ((Fintype.card ι : ℝ) * (1 - q) ^ 2) +
          1 / (Fintype.card ι : ℝ))) * (tolerance : ℝ) ≤
            h * (Fintype.card V : ℝ))
    (hthreshold : ∀ p : Equiv.Perm V,
      SoficGroups.permutationCommutationDefect σ p ≤ 2 * tolerance →
        ∃ U : Finset (V × V),
          ((U ∆ good p).card : ℝ) ≤
            72 * (SoficGroups.boundary
              (fun i => (σ i).prodCongr (σ i)) (good p) : ℝ) /
                ((Fintype.card ι : ℝ) * (1 - q) ^ 2) ∧
          (SoficGroups.boundary
            (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
              (h * (tolerance : ℝ) /
                (2 * (h + 8 * (Fintype.card ι : ℝ)) *
                  (Fintype.card V : ℝ))) * (U.card : ℝ)) :
    SoficGroups.HasAlmostCentralizerImprovement σ tolerance := by
  let d : ℝ := Fintype.card ι
  let C : ℝ := 216 / (d * (1 - q) ^ 2) + 1 / d
  have hd : 0 < d := by
    dsimp [d]
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty ι)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  apply SoficGroups.KunThomFiberCoarea.hasAlmostCentralizerImprovement_of_rooted_reference_cuts
    σ tolerance h hpositive hexp
  intro p hp
  obtain ⟨U, hnear_good, hboundary⟩ := hthreshold p hp
  have hdifference :
      (((U \ SoficGroups.permutationGraph p).card +
        (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) ≤
          C * (tolerance : ℝ) := by
    simpa only [C, d] using
      reference_difference_le_of_good_root_threshold
        σ p B (good p) U tolerance q hq
        (hgood_subset p) (hgood_missing p)
        hbad hp (hgood_boundary p) hnear_good
  have hN : 0 < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr
      (inferInstance : Nonempty V)
  have hcardnat :
      U.card ≤ Fintype.card V +
        ((U \ SoficGroups.permutationGraph p).card +
          (SoficGroups.permutationGraph p \ U).card) := by
    have hinter := Finset.card_sdiff_add_card_inter
      U (SoficGroups.permutationGraph p)
    have hsubset :
        (U ∩ SoficGroups.permutationGraph p).card ≤
          (SoficGroups.permutationGraph p).card :=
      Finset.card_le_card Finset.inter_subset_right
    have hgraph := SoficGroups.KunThomFiberCoarea.permutationGraph_card p
    omega
  have hcard :
      (U.card : ℝ) ≤ (Fintype.card V : ℝ) +
        (((U \ SoficGroups.permutationGraph p).card +
          (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) := by
    exact_mod_cast hcardnat
  have hslow' :
      5 * (4 + h * C) * (tolerance : ℝ) ≤
        h * (Fintype.card V : ℝ) := by
    simpa only [C, d] using hslow
  have hboundary' :
      (SoficGroups.boundary
        (fun i => (σ i).prodCongr (σ i)) U : ℝ) ≤
        (h * (tolerance : ℝ) /
          (2 * (h + 8 * d) * (Fintype.card V : ℝ))) *
            (U.card : ℝ) := by
    simpa only [d] using hboundary
  obtain ⟨hnear, himprovement, hdistance⟩ :=
    rooted_reference_cut_bounds_of_slow_tolerance
      hpositive hd.le hC (Nat.cast_nonneg tolerance) hN
      hdifference hcard hboundary' hslow'
  refine ⟨U, ?_, ?_, ?_⟩
  · exact_mod_cast hnear
  · simpa only [d] using himprovement
  · have hleft :
        ((U \ SoficGroups.permutationGraph p).card : ℝ) ≤
          (((U \ SoficGroups.permutationGraph p).card +
            (SoficGroups.permutationGraph p \ U).card : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right
        (U \ SoficGroups.permutationGraph p).card
        (SoficGroups.permutationGraph p \ U).card
    nlinarith [mul_nonneg hpositive.le
      (sub_nonneg.mpr hleft)]
end SoficGroups.KunUniversalGoodRootReferenceCuts
