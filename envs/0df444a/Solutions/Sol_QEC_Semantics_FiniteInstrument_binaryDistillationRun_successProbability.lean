-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.binaryDistillationRun_successProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:16:39.577088+00:00
-- url     : https://prove2.me/submissions/9aeab46c-4e4a-4b82-9434-da4bea22860a

import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Distillation_Core_FiniteInstrumentBinaryRun

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.FiniteInstrument
open Distillation
open scoped BigOperators
universe u v w
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H]
variable [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K]
variable [FiniteQuantumSystem K]
variable {Resource : Type u}
variable [NormedAddCommGroup Resource] [InnerProductSpace Complex Resource]
variable [FiniteQuantumSystem Resource]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (I : FiniteInstrument kappa Omega H K) (accepts : Omega -> Bool)
    (hI : I.kraus.Complete) (resourceCount : Nat)
    (noisyInput : Fin resourceCount -> DensityOperator Resource)
    (prepareInput :
      (Fin resourceCount -> DensityOperator Resource) -> DensityOperator H)
    (fallback : DensityOperator K) :
    (binaryDistillationRun I accepts hI resourceCount noisyInput prepareInput
      fallback).successProbability =
      (I.binaryCoarsen accepts).bornWeight .accepted
        (prepareInput noisyInput) :=
  rfl
end QEC.Semantics.FiniteInstrument
