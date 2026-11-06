-- Prove2me | solution 1 for QEC.Semantics.FiniteSubsystem.erasureCorrectable_iff
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:49:26.726362+00:00
-- url     : https://prove2.me/submissions/da433941-4044-44b4-9f5e-e8bb58d03bd6

-- ID: b4e56d28-0fb5-4375-88e6-d273552c4ffd | NAME: QEC.Semantics.FiniteSubsystem.erasureCorrectable_iff | 未本地编译验证
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

theorem solution (S : FiniteSubsystem ι) (C : QuantumCode S.factorizedSystem)
    (recovery : QuantumChannel S.complementSystem S.factorizedSystem) :
    S.ErasureCorrectable C recovery ↔
      Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by
  rfl
