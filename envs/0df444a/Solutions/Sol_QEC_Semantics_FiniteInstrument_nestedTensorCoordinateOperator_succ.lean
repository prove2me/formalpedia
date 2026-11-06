-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.nestedTensorCoordinateOperator_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:25:29.170941+00:00
-- url     : https://prove2.me/submissions/17b830c5-b4e8-4f1e-995c-6752e2d4a5ab

import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_FilteredMarginalBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_FilteredBranchOperator
import Definitions.Def_QEC_Semantics_Instruments_Sequential_NestedFilteredMarginalBranchOperator

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
    (L : Type u) [NormedAddCommGroup L] [InnerProductSpace Complex L]
    [FiniteQuantumSystem L] (branches depth : Nat)
    (path : nestedTensorPath branches depth) (port : Fin branches)
    (A : Operator (nestedTensorCarrier L branches (depth + 1))) :
    nestedTensorCoordinateOperator L branches (depth + 1) (path, port) A =
      tensorPowerCoordinateOperator branches port
        (nestedTensorCoordinateOperator
          (tensorPowerCarrier L branches) branches depth path A) := by
  rfl
end QEC.Semantics.FiniteInstrument
