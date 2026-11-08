-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.smallSet_insideAdjacency401
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:25:38.778009+00:00
-- url     : https://prove2.me/submissions/d48ac4b7-eec4-4f0d-8f4f-0adc38bc9fab

import Definitions.Def_QEC_Coding_BalancedProduct_LPSGenerators
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Real.Basic
import Definitions.Def_QEC_Coding_BalancedProduct_LPSGraph
import Theorems.Thm_QEC_Coding_BalancedProduct_LPSGraph_alonChung_insideAdjacency401

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
    (hLPS : LPS401RayleighBound q hq)
    (S : Finset (PGL(2, ZMod q)))
    (hsmall : 10000000 * S.card ≤
      402 * Fintype.card (PGL(2, ZMod q))) :
    25 * insideAdjacencyCount401 q hq S ≤ 1003 * S.card := by
  have halon := alonChung_insideAdjacency401 q hq40 hq hLPS S
  let n : ℝ := Fintype.card (PGL(2, ZMod q))
  let m : ℝ := S.card
  let d : ℝ := insideAdjacencyCount401 q hq S
  have hn : 0 < n := by
    dsimp [n]
    positivity
  have hm : 0 ≤ m := by positivity
  have hsmallR : 10000000 * m ≤ 402 * n := by
    dsimp [m, n]
    exact_mod_cast hsmall
  change 10 * n * d ≤ 401 * m * (n - m) + 4020 * m ^ 2 at halon
  have hreal : 25 * d ≤ 1003 * m := by
    nlinarith
  dsimp [d, m] at hreal
  exact_mod_cast hreal
end QEC.Coding.BalancedProduct.LPSGraph
