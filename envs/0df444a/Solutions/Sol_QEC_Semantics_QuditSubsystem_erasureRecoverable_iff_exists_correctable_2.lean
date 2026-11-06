-- Prove2me | solution 2 for QEC.Semantics.QuditSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:02:28.865215+00:00
-- url     : https://prove2.me/submissions/02362387-bbc2-4d1d-a41b-26d859e2ef9d

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery :=
  Iff.rfl
end QEC.Semantics.QuditSubsystem
