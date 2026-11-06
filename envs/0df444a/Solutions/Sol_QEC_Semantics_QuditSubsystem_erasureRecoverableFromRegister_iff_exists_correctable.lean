-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureRecoverableFromRegister_iff_exists_correctable
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T17:55:04.877771+00:00
-- url     : https://prove2.me/submissions/eabc47eb-21ff-46e8-8a18-767c7fae8008

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
    (C : QuantumCode (Qudit.QuditRegister q)) :
    S.ErasureRecoverableFromRegister C ↔
      ∃ recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q),
        Correctable (Qudit.QuditRegister q) S.complementSystem C
          S.erasureChannelFromRegister recovery := by
  solve | rfl | simp [QuditRegister, QuditSubsystem, complementSystem, erasureChannelFromRegister, ErasureRecoverableFromRegister] | simp_all [QuditRegister, QuditSubsystem, complementSystem, erasureChannelFromRegister, ErasureRecoverableFromRegister] | omega | norm_num
