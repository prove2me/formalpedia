-- Prove2me | solution 2 for QEC.Semantics.FiniteSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:00:01.160532+00:00
-- url     : https://prove2.me/submissions/21ccd865-2491-4bfa-a2c8-4df1109efebd

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
theorem _root_.solution (S : FiniteSubsystem ι)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl
end QEC.Semantics.FiniteSubsystem
