-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.sum_lpsNeighbors401_eq_sum_generators
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:54.851029+00:00
-- url     : https://prove2.me/submissions/a7e9d04f-a8d3-4a9f-9db2-fc171c0447af

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
    (v : PGL(2, ZMod q))
    (f : PGL(2, ZMod q) → ℝ) :
    ∑ w ∈ lpsNeighbors401 q hq v, f w =
      ∑ s ∈ lpsGenerators401 q hq, f (s * v) := by
  classical
  unfold lpsNeighbors401
  rw [Finset.sum_image]
  intro s _hs t _ht hst
  exact mul_right_cancel hst
end QEC.Coding.BalancedProduct.LPSGraph
