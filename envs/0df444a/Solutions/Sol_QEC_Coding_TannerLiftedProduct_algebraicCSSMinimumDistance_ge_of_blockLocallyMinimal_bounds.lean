-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.algebraicCSSMinimumDistance_ge_of_blockLocallyMinimal_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T08:37:52.89027+00:00
-- url     : https://prove2.me/submissions/65cea95a-d19e-4a8f-ab5d-48b72ae74e9d

import Definitions.Def_QEC_Coding_ExpanderCodes_TannerLiftedProduct
import Definitions.Def_QEC_Coding_ExpanderCodes_LocallyMinimalDistance
import Definitions.Def_QEC_Coding_ExpanderCodes_LocalStarExpansion
import Definitions.Def_QEC_Coding_ExpanderCodes_TannerBlockWeight
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_blockWeight_le_hammingWeight
import Theorems.Thm_QEC_Coding_LocallyMinimalDistance_chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds


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
        (LocallyMinimalDistance.elementaryBoundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hcocycles : ∀ c,
      c ∈ (chainComplex label h g').middleCocycleCode.carrier → c ≠ 0 →
      LocallyMinimalDistance.IsLocallyMinimal blockWeight
        (LocallyMinimalDistance.elementaryCoboundaryMoves
          (chainComplex label h g')) c →
      lowerBound ≤ blockWeight c)
    (hminimum : AlgebraicCSSMinimumDistance
      (chainComplex label h g').firstCoboundaryCheckCode
      (chainComplex label h g').middleBoundaryCode d) :
    lowerBound ≤ d := by
  exact LocallyMinimalDistance.chainComplex_algebraicCSSMinimumDistance_ge_of_locallyMinimal_bounds
      (chainComplex label h g') blockWeight lowerBound d
      blockWeight_le_hammingWeight hcycles hcocycles hminimum
end QEC.Coding.TannerLiftedProduct
