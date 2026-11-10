-- Prove2me | solution 1 for QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.physicalU13_symm_magicRegisterKet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:49:39.405138+00:00
-- url     : https://prove2.me/submissions/a10a8ff1-3397-4a22-ba87-9c28f25b6398

import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_MagicResource
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19MagicResource
open Semantics
open QEC.Distillation.KT19PrimeQuditCSS
open scoped BigOperators
open QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
universe u v w
variable (p : Nat) [NeZero p]
variable {Site : Type u} [Fintype Site]
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS._p2m_local_instance_d135975d44_41
attribute [local instance] QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS.primeQuditRegisterLabelFintypeLocal
namespace QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
theorem _root_.solution (e : PrimeQuditRegisterLabel p Site) :
    (physicalU13 p).symm (magicRegisterKet p e) = characterKet p e := by
  ext x
  rw [physicalU13_symm_apply_phase, magicRegisterKet_apply, characterKet_apply]
  rw [← mul_assoc, mul_comm _ ((Real.sqrt (p : Real) : Complex)⁻¹ ^ Fintype.card Site)]
  rw [mul_assoc, ← phase_add]
  rw [show -cubicExponent p x + (registerPairing p e x + cubicExponent p x) =
      registerPairing p e x by abel]
end QEC.Distillation.KT19MagicResource.KT19PrimeQuditCSS
