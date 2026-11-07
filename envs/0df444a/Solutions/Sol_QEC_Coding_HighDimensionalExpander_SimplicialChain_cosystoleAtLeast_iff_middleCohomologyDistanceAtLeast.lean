-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SimplicialChain.cosystoleAtLeast_iff_middleCohomologyDistanceAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:06:03.375204+00:00
-- url     : https://prove2.me/submissions/2235c4d2-f785-4983-8aac-1d1ed14d9f15

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
    CosystoleAtLeast K p d ↔
      MiddleCohomologyDistanceAtLeast (chainComplexAt K p) d := by
  rfl
end QEC.Coding.HighDimensionalExpander.SimplicialChain
