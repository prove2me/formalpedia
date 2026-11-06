-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.erasureChannelFromRegister_comp_prepareSelected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:18:18.797149+00:00
-- url     : https://prove2.me/submissions/43dee232-2fb9-4a41-9c9a-8c9389525279

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Semantics_Channels_Kraus
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Theorems.Thm_QEC_Semantics_QuditSubsystem_quantumChannel_ext
import Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureChannelFromRegister_prepareSelected_apply

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open QEC.Semantics.QuditSubsystem
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (S : QuditSubsystem q)
    (rho : DensityOperator S.selectedSystem) :
    QuantumChannel.comp S.erasureChannelFromRegister (S.prepareSelected rho) =
      QuantumChannel.id S.complementSystem := by
  apply quantumChannel_ext
  apply LinearMap.ext
  intro A
  exact S.erasureChannelFromRegister_prepareSelected_apply rho A
end QEC.Semantics.QuditSubsystem
