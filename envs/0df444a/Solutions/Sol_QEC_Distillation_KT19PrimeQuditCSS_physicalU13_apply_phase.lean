-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_phase
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:46:11.585214+00:00
-- url     : https://prove2.me/submissions/482d6a94-ed3a-4f4f-a301-a21f95b00237

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_phase_fintype_sum
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site]
    (psi : PrimeQuditRegister p Site) (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p psi label = phase p (cubicExponent p label) * psi label := by
  rw [physicalU13_apply]
  change (∏ site : Site, phase p (label site ^ 3)) * psi label = _
  rw [phase_fintype_sum]
  rfl
end QEC.Distillation.KT19PrimeQuditCSS
