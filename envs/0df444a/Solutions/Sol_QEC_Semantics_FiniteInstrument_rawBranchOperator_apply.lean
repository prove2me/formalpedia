-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.rawBranchOperator_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:51:56.021196+00:00
-- url     : https://prove2.me/submissions/db659934-9805-4759-baae-370d25656d68

import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ConditionedChannel
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_BornMass

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
theorem _root_.solution (I : FiniteInstrument κ Ω H K) (index : κ)
    (A : Operator H) :
    I.rawBranchOperator index A =
      (I.kraus.operator index).comp
        (A.comp (LinearMap.adjoint (I.kraus.operator index))) :=
  rfl
end QEC.Semantics.FiniteInstrument
