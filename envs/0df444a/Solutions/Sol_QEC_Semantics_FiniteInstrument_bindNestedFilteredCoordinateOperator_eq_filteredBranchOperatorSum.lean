-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.bindNestedFilteredCoordinateOperator_eq_filteredBranchOperatorSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:39:00.510986+00:00
-- url     : https://prove2.me/submissions/4be55193-1d5c-4c30-9a33-f8b986949829

import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator
import Theorems.Thm_QEC_Semantics_FiniteInstrument_bind_nestedTensor_coordinateOperator_branchOperator_filter_sum_eq

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {kappaTwo : Type x} [Fintype kappaTwo]
variable {Xi : Type y} [Fintype Xi]
variable {H K L : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
variable [NormedAddCommGroup L] [InnerProductSpace Complex L] [FiniteQuantumSystem L]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (branches depth : Nat)
    (I : FiniteInstrument kappa Omega H
      (nestedTensorCarrier K branches depth))
    (J : FiniteInstrument kappaTwo Xi K L) (hJ : J.kraus.Complete)
    (firstPredicate : Omega -> Prop) [DecidablePred firstPredicate]
    (secondPredicate : Xi -> Prop) [DecidablePred secondPredicate]
    (path : nestedTensorPath branches depth)
    (A : Operator H) :
    bindNestedFilteredCoordinateOperator branches depth I J
        firstPredicate secondPredicate path A =
      filteredBranchOperatorSum J secondPredicate
        (nestedFilteredPredecessorCoordinateOperator branches depth I
          firstPredicate path A) := by
  exact bind_nestedTensor_coordinateOperator_branchOperator_filter_sum_eq
    branches depth I J hJ firstPredicate secondPredicate path A
end QEC.Semantics.FiniteInstrument
