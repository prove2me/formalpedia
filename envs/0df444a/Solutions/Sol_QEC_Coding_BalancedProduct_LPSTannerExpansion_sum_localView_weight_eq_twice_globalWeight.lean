-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.sum_localView_weight_eq_twice_globalWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:43:21.170986+00:00
-- url     : https://prove2.me/submissions/73264e88-d785-462a-ba5e-d55233f5d1a1

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_card_wordSupportGraph_edges
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTannerExpansion_localView_weight_eq_support_degree

set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus
namespace QEC.Coding.BalancedProduct.LPSTannerExpansion
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (x : Word (ZMod 2) (Edge401 q hq)) :
    (∑ g, HammingWeight (localView q hq40 hq g x)) =
      2 * HammingWeight x := by
  simp_rw [localView_weight_eq_support_degree q hq40 hq x]
  rw [(wordSupportGraph q hq x).sum_degrees_eq_twice_card_edges]
  rw [SimpleGraph.edgeFinset_card, card_wordSupportGraph_edges q hq x]
end QEC.Coding.BalancedProduct.LPSTannerExpansion
