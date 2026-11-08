-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.card_lpsNeighbors401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:21:48.016562+00:00
-- url     : https://prove2.me/submissions/a2fe66e0-4c1b-4470-bc41-9d568f38be63

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGenerators_card_lpsGenerators401


set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq40 : 40 < q)
    (hq : legendreSym q 401 = -1)
    (g : PGL(2, ZMod q)) :
    (lpsNeighbors401 q hq g).card = 402 := by
  classical
  rw [lpsNeighbors401, Finset.card_image_of_injective]
  · exact card_lpsGenerators401 q hq40 hq
  · intro s t h
    exact mul_right_cancel h
end QEC.Coding.BalancedProduct.LPSGraph
