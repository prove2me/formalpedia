-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:27:29.148132+00:00
-- url     : https://prove2.me/submissions/d96d1d10-6e1b-42e0-9004-9a1d9a2ddf75

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localView_basis_of_endpoint
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localView_basis_of_not_endpoint
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_apply

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
    (g : Vertex401 q) (j : Fin 200) :
    tannerBoundary q hq40 hq (canonicalBasisWord e) (g, j) =
      if hg : g ∈ e.1 then
        localCheckCoefficient (edgeLocalCoordinate q hq40 hq e g hg) j
      else 0 := by
  split_ifs with hg
  · rw [tannerBoundary_apply, localView_basis_of_endpoint q hq40 hq e g hg]
    rfl
  · rw [tannerBoundary_apply, localView_basis_of_not_endpoint q hq40 hq e g hg]
    exact congrFun localParityCheck.map_zero j
end QEC.Coding.BalancedProduct.LPSTanner
