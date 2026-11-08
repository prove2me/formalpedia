-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_fiberLocallyMinimal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:38:02.731945+00:00
-- url     : https://prove2.me/submissions/ab9671e8-36c4-4790-8495-a3440b0d6b15

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_le_hammingWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_horizontalFiberBoundaryMoves_subset_middleBoundaryCode
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_weight_ge_of_locallyMinimal_cycle_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
universe u v
variable {F : Type u} {G W R R' : Type v}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Group G] [Fintype G] [DecidableEq G]
variable [Fintype W] [DecidableEq W]
variable [Fintype R] [DecidableEq R]
variable [Fintype R'] [DecidableEq R']
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (label : W → G) (h : Matrix R W F) (g' : Matrix R' W F)
    (lowerBound d : Nat)
    (hcycles : ∀ c,
      c ∈ (chainComplex label h g').middleCycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (horizontalFiberBoundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (verticalFiberCoboundaryMoves label h g') c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by
  let K := chainComplex label h g'
  rcases hminimum with ⟨c, hc, hdistance, _⟩
  rw [← hdistance]
  rcases hc with hcX | hcZ
  · have hcCocycle : c ∈ K.middleCocycleCode.carrier := by
      rw [← K.middleBoundaryCode_dual_carrier_eq_middleCocycleCode]
      exact hcX.1
    have hBlock := LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
      blockWeight K.middleCocycleCode.carrier.toAddSubgroup
      K.firstCoboundaryCheckCode.carrier.toAddSubgroup
      (verticalFiberCoboundaryMoves label h g')
      K.firstCoboundaryCheckCode_le_middleCocycleCode
      (verticalFiberCoboundaryMoves_subset_firstCoboundaryCheckCode
        label h g') lowerBound hcocycles c hcCocycle hcX.2
    exact hBlock.trans (blockWeight_le_hammingWeight c)
  · have hcCycle : c ∈ K.middleCycleCode.carrier := by
      rw [← K.firstCoboundaryCheckCode_dual_carrier_eq_middleCycleCode]
      exact hcZ.1
    have hBlock := LocallyMinimalDistance.weight_ge_of_locallyMinimal_cycle_bound
      blockWeight K.middleCycleCode.carrier.toAddSubgroup
      K.middleBoundaryCode.carrier.toAddSubgroup
      (horizontalFiberBoundaryMoves label h g')
      K.middleBoundaryCode_le_middleCycleCode
      (horizontalFiberBoundaryMoves_subset_middleBoundaryCode
        label h g') lowerBound hcycles c hcCycle hcZ.2
    exact hBlock.trans (blockWeight_le_hammingWeight c)
end QEC.Coding.TannerLiftedProduct
