-- Prove2me | solution 1 for QEC.Coding.BDL26TannerLocalRegularity.totalParity_graphBoundary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:29:57.47159+00:00
-- url     : https://prove2.me/submissions/2636a61a-7e9d-460e-81ca-9b9bf65c1cf3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_TannerSquare
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalRegularity

set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.BDL26TannerLocalRegularity
open Module
open BDL26FiniteAlternatingCore
open BDL26FiniteTannerSquare
universe u
namespace QEC.Coding.BDL26TannerLocalRegularity
theorem _root_.solution {Vertex Edge : Type}
    [Fintype Vertex] [Fintype Edge] [DecidableEq Vertex]
    (edgeStart edgeEnd : Edge → Vertex) (chain : Word Field Edge) :
    totalParity (graphBoundary edgeStart edgeEnd chain) = 0 := by
  classical
  change (∑ vertex : Vertex, ∑ edge : Edge,
    chain edge * graphEdgeBoundary edgeStart edgeEnd edge vertex) = 0
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro edge _
  rw [← Finset.mul_sum]
  change chain edge * totalParity
    (graphEdgeBoundary edgeStart edgeEnd edge) = 0
  rw [totalParity_graphEdgeBoundary, mul_zero]
end QEC.Coding.BDL26TannerLocalRegularity
