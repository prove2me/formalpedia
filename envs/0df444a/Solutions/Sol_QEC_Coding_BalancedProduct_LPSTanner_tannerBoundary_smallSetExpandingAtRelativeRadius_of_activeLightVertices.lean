-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_smallSetExpandingAtRelativeRadius_of_activeLightVertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:44:00.791795+00:00
-- url     : https://prove2.me/submissions/3540e2e0-e5aa-41f6-b483-13122fb86d55

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_card_activeLightVertices_le_boundary_weight

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
    (hactive : ∀ x : Word (ZMod 2) (Edge401 q hq),
      radiusDenominator * HammingWeight x ≤
          radiusNumerator * Fintype.card (Edge401 q hq) →
      expansionNumerator * HammingWeight x ≤
        expansionDenominator *
          (activeLightVertices q hq40 hq x).card) :
    (tannerBoundary q hq40 hq).SmallSetExpandingAtRelativeRadius
      radiusNumerator radiusDenominator
      expansionNumerator expansionDenominator := by
  refine ⟨hradius, hexpansion, ?_⟩
  intro x hx
  exact (hactive x hx).trans <|
    Nat.mul_le_mul_left expansionDenominator
      (card_activeLightVertices_le_boundary_weight q hq40 hq x)
end QEC.Coding.BalancedProduct.LPSTanner
