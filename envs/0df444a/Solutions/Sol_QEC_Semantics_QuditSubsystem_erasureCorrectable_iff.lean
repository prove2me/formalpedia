-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureCorrectable_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:46:33.21291+00:00
-- url     : https://prove2.me/submissions/e2248379-a5c9-4b45-9ca5-9da88d70c10e

-- ID: 1466a5b1-d6a5-4206-beda-42ece45d5b7f | NAME: QEC.Semantics.QuditSubsystem.erasureCorrectable_iff | 未本地编译验证
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

theorem solution (S : QuditSubsystem q) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by
  rfl
