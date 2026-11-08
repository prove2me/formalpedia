-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSTanner.incidentAsEdge_edgeAsIncident
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:23:26.062384+00:00
-- url     : https://prove2.me/submissions/22a93ded-3d4a-4482-984e-16b400657e0f

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
    (hq : legendreSym q 401 = -1)
    (e : Edge401 q hq) (g : Vertex401 q)
    (hg : g ∈ e.1) :
    incidentAsEdge q hq (edgeAsIncident q hq e g hg) = e := by
  rfl
end QEC.Coding.BalancedProduct.LPSTanner
