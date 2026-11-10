-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13ConjugatedX_firstDifference_is_pauli
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:45:13.125105+00:00
-- url     : https://prove2.me/submissions/7b4d72a7-6758-4bf4-ac7d-2f2f833a7c2a

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_u13ConjugatedXExponent_firstDifference

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] (x : ZMod p) :
    phase p (u13ConjugatedXExponent p (x + 1) - u13ConjugatedXExponent p x) =
      phase p 6 * zPowerAmplitude p 6 x := by
  rw [u13ConjugatedXExponent_firstDifference]
  change phase p (6 * x + 6) = phase p 6 * phase p (6 * x)
  rw [phase_add, mul_comm]
end QEC.Distillation.KT19PrimeQuditCSS
