-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecoverable_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:46:50.525894+00:00
-- url     : https://prove2.me/submissions/8ddf5af3-f3f3-4186-ae12-7e050eeced98

-- ID: d467e417-4266-496c-8fa8-3a099b26a556 | NAME: QEC.Semantics.QuditSubsystem.erasureRecoverable_iff_exists_correctable | 未本地编译验证
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

theorem solution (S : QuditSubsystem q)
    (C : QuantumCode S.factorizedSystem) :
    S.ErasureRecoverable C ↔
      ∃ recovery : QuantumChannel S.complementSystem S.factorizedSystem,
        Correctable S.factorizedSystem S.complementSystem C S.erasureChannel recovery := by
  rfl
