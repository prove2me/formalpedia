-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SimplicialChain.systoleAtLeast_iff_middleHomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:00.882824+00:00
-- url     : https://prove2.me/submissions/e6e2914b-ec28-476f-a9f1-0637d89342a3

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.AlgebraicTopology.SimplicialComplex.Basic
import Mathlib.Data.Finset.Interval
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.SimplicialChain
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (K : AbstractSimplicialComplex V)
namespace QEC.Coding.HighDimensionalExpander.SimplicialChain
theorem _root_.solution
    (p d : Nat) :
    SystoleAtLeast K p d ↔
      MiddleHomologyDistanceAtLeast (chainComplexAt K p) d := by
  rfl
end QEC.Coding.HighDimensionalExpander.SimplicialChain
