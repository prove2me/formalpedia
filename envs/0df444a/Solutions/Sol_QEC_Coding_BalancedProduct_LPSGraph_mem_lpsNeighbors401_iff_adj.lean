-- Prove2me | solution 1 for QEC.Coding.BalancedProduct.LPSGraph.mem_lpsNeighbors401_iff_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:20.610541+00:00
-- url     : https://prove2.me/submissions/88053de8-c36a-4aa2-8916-f3eb78b03ee8

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
    (g w : PGL(2, ZMod q)) :
    w ∈ lpsNeighbors401 q hq g ↔
      (lpsCayleyGraph401 q hq).Adj g w := by
  classical
  rw [lpsCayleyGraph401_adj_iff]
  constructor
  · intro hw
    change w ∈ (lpsGenerators401 q hq).image (fun s => s * g) at hw
    rcases Finset.mem_image.mp hw with ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    change s * g ∈ (lpsGenerators401 q hq).image (fun a => a * g)
    exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
end QEC.Coding.BalancedProduct.LPSGraph
