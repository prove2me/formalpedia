-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.transpose_tannerBoundary_smallSetExpandingAtRelativeRadius_of_dualExposed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:22.910809+00:00
-- url     : https://prove2.me/submissions/97eb83e1-83b4-401b-b3b0-73bf6dfd0e38

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_card_dualExposedVertices_le_transpose_weight

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTanner
open Classical
open GVPlus LPSGenerators LPSGraph
attribute [local instance] QEC.Coding.BalancedProduct.LPSTanner.edge401Fintype
namespace QEC.Coding.BalancedProduct.LPSTanner
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator : ℕ)
    (hradius : 0 < radiusDenominator)
    (hexpansion : 0 < expansionDenominator)
    (hexposed : ∀ y : Word (ZMod 2) (Check401 q),
      radiusDenominator * HammingWeight y ≤
          radiusNumerator * Fintype.card (Check401 q) →
      expansionNumerator * HammingWeight y ≤
        expansionDenominator *
          (dualExposedVertices q hq40 hq y).card) :
    (wordLinearMapTranspose
      (tannerBoundary q hq40 hq)).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hradius, hexpansion, ?_⟩
  intro y hy
  exact (hexposed y hy).trans <|
    Nat.mul_le_mul_left expansionDenominator
      (card_dualExposedVertices_le_transpose_weight q hq40 hq y)
end QEC.Coding.BalancedProduct.LPSTanner
