-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.tannerBoundary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:23:38.348123+00:00
-- url     : https://prove2.me/submissions/2005259e-118f-4a81-8f65-196c347fe3b8

import Definitions.Def_QEC_Coding_BalancedProduct_GVPlus
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Definitions.Def_QEC_Coding_BalancedProduct_TannerExpansion
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Fintype.Units
import Definitions.Def_QEC_Coding_BalancedProduct_LPSTanner

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
    (g : Vertex401 q) (j : Fin 200) :
    tannerBoundary q hq40 hq x (g, j) =
      localParityCheck (localView q hq40 hq g x) j :=
  rfl
end QEC.Coding.BalancedProduct.LPSTanner
