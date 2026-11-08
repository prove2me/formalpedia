-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_neighbor_vertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:23.800916+00:00
-- url     : https://prove2.me/submissions/d703de63-fe6d-4b99-b1e7-9f919d8e88c6

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph

set_option autoImplicit false
open scoped MatrixGroups
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.LPSGraph
open Matrix
open LPSArithmetic LPSGenerators
namespace QEC.Coding.BalancedProduct.LPSGraph
theorem _root_.solution
    (q : ℕ) [Fact q.Prime]
    (hq : legendreSym q 401 = -1)
    (S : Finset (PGL(2, ZMod q)))
    (v : PGL(2, ZMod q)) :
    ∑ w ∈ lpsNeighbors401 q hq v, vertexIndicator401 q S w =
      (lpsNeighborsIn401 q hq S v).card := by
  classical
  unfold lpsNeighborsIn401
  change
    (∑ w ∈ lpsNeighbors401 q hq v,
      if w ∈ S then (1 : ℝ) else 0) =
        ((lpsNeighbors401 q hq v).filter (· ∈ S)).card
  rw [Finset.sum_boole]
end QEC.Coding.BalancedProduct.LPSGraph
