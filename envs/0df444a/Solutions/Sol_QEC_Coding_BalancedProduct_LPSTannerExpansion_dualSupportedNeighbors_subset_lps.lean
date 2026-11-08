-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTannerExpansion.dualSupportedNeighbors_subset_lps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:41:00.701607+00:00
-- url     : https://prove2.me/submissions/6f4cc24a-a752-4855-9147-69001dac5f1a

import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTannerExpansion
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_mem_lpsNeighbors401_iff_adj


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
    (y : Word (ZMod 2) (Check401 q))
    (g : Vertex401 q) :
    dualSupportedNeighbors q hq40 hq y g ⊆ lpsNeighbors401 q hq g := by
  intro w hw
  rcases Finset.mem_map.1 hw with ⟨a, ha, rfl⟩
  exact (LPSGraph.mem_lpsNeighbors401_iff_adj q hq g _).2
    (localCoordinateNeighborEquiv q hq40 hq g a).2
end QEC.Coding.BalancedProduct.LPSTannerExpansion
