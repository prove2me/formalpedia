-- Prove2me | solution 1 for SimpleGraph.lineGraph_chromaticNumber_le_maxDegree_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:11:22.812927+00:00
-- url     : https://prove2.me/submissions/12c33238-bbd0-4bda-b2d6-72db13eb4e8d

module
public import Definitions.Def_LeanPool_Vizing_Step
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Definitions.Def_LeanPool_Vizing_Main
public import Theorems.Thm_LeanPool_Vizing_lineGraph_colorable
public import Theorems.Thm_LeanPool_Vizing_PEC_kempeSwap_col
public import Theorems.Thm_LeanPool_Vizing_PEC_setEdge_col
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_left
public import Theorems.Thm_LeanPool_Vizing_PEC_updFun_right
attribute [local simp] LeanPool.Vizing.PEC.kempeSwap_col
attribute [local simp] LeanPool.Vizing.PEC.setEdge_col
attribute [local simp] LeanPool.Vizing.PEC.updFun_left
attribute [local simp] LeanPool.Vizing.PEC.updFun_right



set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open SimpleGraph
namespace SimpleGraph
theorem _root_.solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.lineGraph).chromaticNumber ≤ (G.maxDegree : ℕ∞) + 1 := by
  have h : (G.lineGraph).Colorable (G.maxDegree + 1) := LeanPool.Vizing.lineGraph_colorable G
  have := h.chromaticNumber_le
  simpa only [Nat.cast_add, Nat.cast_one] using this
end SimpleGraph
