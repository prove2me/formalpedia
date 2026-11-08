-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_vertexIndicator401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:16.108343+00:00
-- url     : https://prove2.me/submissions/893547af-ddc4-4e73-beac-286bf08e5d0a

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
    (S : Finset (PGL(2, ZMod q))) :
    ∑ v, vertexIndicator401 q S v = S.card := by
  classical
  change (∑ v ∈ Finset.univ, if v ∈ S then (1 : ℝ) else 0) = S.card
  rw [Finset.sum_boole]
  simp
end QEC.Coding.BalancedProduct.LPSGraph
