-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.exists_violated_check_at_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:40:11.736261+00:00
-- url     : https://prove2.me/submissions/48e4fab0-1eec-481d-8dfa-e5120b287cea

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_tannerBoundary_apply
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSTanner_localParityCheck_ne_zero_of_ne_zero_of_weight_lt

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
    (x : Word (ZMod 2) (Edge401 q hq))
    (g : Vertex401 q)
    (hlocal0 : localView q hq40 hq g x ≠ 0)
    (hlocalWeight : HammingWeight (localView q hq40 hq g x) < 41) :
    ∃ j : Fin 200, tannerBoundary q hq40 hq x (g, j) ≠ 0 := by
  have hsyndrome :=
    localParityCheck_ne_zero_of_ne_zero_of_weight_lt
      (localView q hq40 hq g x) hlocal0 hlocalWeight
  by_contra hnone
  apply hsyndrome
  funext j
  rw [← tannerBoundary_apply q hq40 hq x g j]
  exact not_ne_iff.mp ((not_exists.mp hnone) j)
end QEC.Coding.BalancedProduct.LPSTanner
