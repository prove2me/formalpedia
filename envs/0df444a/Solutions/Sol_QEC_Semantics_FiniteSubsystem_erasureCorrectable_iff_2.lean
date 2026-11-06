-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.erasureCorrectable_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:59:59.958189+00:00
-- url     : https://prove2.me/submissions/1c1b3ad7-75bc-4c4a-b75c-94c379e0d5c3

import Definitions.Def_QEC_Semantics_Channels_Core
import Definitions.Def_QEC_Semantics_Core_Qubit
import Definitions.Def_QEC_Semantics_Core_Subsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u
open QEC.Semantics.FiniteSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
namespace QEC.Semantics.FiniteSubsystem
theorem _root_.solution (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl
end QEC.Semantics.FiniteSubsystem
