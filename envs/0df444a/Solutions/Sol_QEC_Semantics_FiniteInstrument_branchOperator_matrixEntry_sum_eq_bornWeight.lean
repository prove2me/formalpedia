-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.branchOperator_matrixEntry_sum_eq_bornWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:35:55.411975+00:00
-- url     : https://prove2.me/submissions/316f2af8-61f2-4f4a-a7c5-e27c211916ad

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BranchOperator

set_option autoImplicit false
universe u v w x y
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {κ : Type v} [Fintype κ]
variable {Ω : Type w} [Fintype Ω]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    {β : Type y} [Fintype β] (basis : OrthonormalBasis β Complex K)
    (I : FiniteInstrument κ Ω H K) (outcome : Ω) (rho : DensityOperator H) :
    (∑ index : β,
        inner Complex (basis index)
          (I.branchOperator outcome rho.toOperator (basis index))) =
      (I.bornWeight outcome rho : Complex) := by
  calc
    (∑ index : β,
        inner Complex (basis index)
          (I.branchOperator outcome rho.toOperator (basis index))) =
        LinearMap.trace Complex K
          (I.branchOperator outcome rho.toOperator) :=
      (LinearMap.trace_eq_sum_inner
        (I.branchOperator outcome rho.toOperator) basis).symm
    _ = (I.bornWeight outcome rho : Complex) :=
      I.trace_branchOperator_eq_bornWeight outcome rho
end QEC.Semantics.FiniteInstrument
