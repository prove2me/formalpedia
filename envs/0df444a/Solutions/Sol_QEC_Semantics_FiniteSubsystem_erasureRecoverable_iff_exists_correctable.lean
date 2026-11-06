-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:51:45.176499+00:00
-- url     : https://prove2.me/submissions/a16f3c9f-2fe5-4aa4-9cc0-a40817b0c828

-- ID: 7cae4629-8ffe-4b7a-b101-fb507c04a656 | NAME: QEC.Semantics.FiniteSubsystem.erasureRecoverable_iff_exists_correctable | 未本地编译验证
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

theorem solution (S : FiniteSubsystem ι)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by
  rfl
