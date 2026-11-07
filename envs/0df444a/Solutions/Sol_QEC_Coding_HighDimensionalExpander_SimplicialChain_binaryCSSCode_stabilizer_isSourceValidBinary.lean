-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.SimplicialChain.binaryCSSCode_stabilizer_isSourceValidBinary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:57.064363+00:00
-- url     : https://prove2.me/submissions/91395233-798f-4adc-b569-7bec93a68cfa

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
theorem _root_.solution (p : Nat) :
    ((chainComplexAt K p).binaryCSSCode).stabilizer.IsSourceValidBinary :=
  ChainComplexData.binaryCSSCode_stabilizer_isSourceValidBinary
    (chainComplexAt K p)
end QEC.Coding.HighDimensionalExpander.SimplicialChain
