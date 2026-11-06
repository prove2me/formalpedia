-- Prove2me | solution 1 for QEC.Semantics.FiniteInstrument.tensorPowerQubitBitstringEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:50:10.847325+00:00
-- url     : https://prove2.me/submissions/5dd20a2b-769f-472d-8867-76ab0e8e424b

import Definitions.Def_QEC_Semantics_Instruments_Selection_Selection
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_Basis

set_option autoImplicit false
universe u v
open QEC
open QEC.Semantics
noncomputable section
open QEC.Semantics.FiniteInstrument
open scoped TensorProduct
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
  [FiniteQuantumSystem H]
variable {β : Type v} [Fintype β]
namespace QEC.Semantics.FiniteInstrument
theorem _root_.solution
    (ι : Type u) [Fintype ι] (attempts : Nat)
    (history : tensorPowerHistory (Qubit.Bitstring ι) attempts)
    (trial : Fin attempts) (coordinate : ι) :
    tensorPowerQubitBitstringEquiv ι attempts history (trial, coordinate) =
      tensorPowerHistoryAt (Qubit.Bitstring ι) attempts history trial coordinate :=
  rfl
end QEC.Semantics.FiniteInstrument
