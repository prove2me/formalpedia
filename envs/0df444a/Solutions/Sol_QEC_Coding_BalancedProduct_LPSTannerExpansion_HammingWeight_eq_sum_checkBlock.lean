-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.HammingWeight_eq_sum_checkBlock
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:29:52.477079+00:00
-- url     : https://prove2.me/submissions/b99ed521-e33a-4864-a68a-82da8630e721

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
section
noncomputable section
open scoped MatrixGroups
namespace QEC.Coding.BalancedProduct.LPSTannerExpansion
open Classical
open QEC.Coding
open QEC.Coding.BalancedProduct
open LPSTanner LPSGraph GVPlus
private theorem hammingWeight_eq_sum_indicator
    {F : Type*} [Zero F] [DecidableEq F]
    {ι : Type*} [Fintype ι] (z : Word F ι) :
    HammingWeight z = ∑ i, if z i ≠ 0 then 1 else 0 := by
  classical
  rw [HammingWeight, hammingSupport, Finset.card_filter]
end QEC.Coding.BalancedProduct.LPSTannerExpansion
end
end

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
    (y : Word (ZMod 2) (Check401 q)) :
    HammingWeight y = ∑ g, HammingWeight (checkBlock q g y) := by
  rw [hammingWeight_eq_sum_indicator]
  simp_rw [hammingWeight_eq_sum_indicator]
  change (∑ p : Vertex401 q × Fin 200, if y p ≠ 0 then 1 else 0) =
    ∑ g : Vertex401 q, ∑ j : Fin 200, if y (g, j) ≠ 0 then 1 else 0
  exact Fintype.sum_prod_type _
end QEC.Coding.BalancedProduct.LPSTannerExpansion
