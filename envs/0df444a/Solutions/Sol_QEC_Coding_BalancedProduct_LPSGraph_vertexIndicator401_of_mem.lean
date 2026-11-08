-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.vertexIndicator401_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:17.574534+00:00
-- url     : https://prove2.me/submissions/dfd864d0-5c05-4ec1-8f80-cc3ad6e7b23a

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
    (S : Finset (PGL(2, ZMod q)))
    {v : PGL(2, ZMod q)} (hv : v ∈ S) :
    vertexIndicator401 q S v = 1 := by
  classical
  change (if v ∈ S then (1 : ℝ) else 0) = 1
  rw [if_pos hv]
end QEC.Coding.BalancedProduct.LPSGraph
