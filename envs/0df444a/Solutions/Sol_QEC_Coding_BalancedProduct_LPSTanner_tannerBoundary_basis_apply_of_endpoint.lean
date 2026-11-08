-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply_of_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:29:41.419121+00:00
-- url     : https://prove2.me/submissions/95ac14c4-c7c8-4266-b263-3f7ab5316702

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_basis_apply

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
    (e : Edge401 q hq)
    (g : Vertex401 q) (j : Fin 200)
    (hg : g ∈ e.1) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      localCheckCoefficient
        (edgeLocalCoordinate q hq40 hq e g hg) j := by
  rw [tannerBoundary_basis_apply]
  split
  · rfl
  · contradiction
end QEC.Coding.BalancedProduct.LPSTanner
