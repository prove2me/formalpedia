-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.xTransport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:42:43.959199+00:00
-- url     : https://prove2.me/submissions/c6b074e7-b7f5-49e9-87d6-792430a02fc7

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.KT19PrimeQuditCSS
open Semantics
open scoped BigOperators
universe u
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] (x : ZMod p) :
    xTransport p (quditBasisKet p x) = quditBasisKet p (x + 1) := by
  classical
  ext target
  by_cases htarget : target = x + 1
  · subst target
    simp [xTransport_apply, quditBasisKet, EuclideanSpace.basisFun_apply]
  · have htarget' : target - 1 ≠ x := by
      intro h
      apply htarget
      calc
        target = (target - 1) + 1 := by ring
        _ = x + 1 := by rw [h]
    simp [xTransport_apply, quditBasisKet, EuclideanSpace.basisFun_apply, htarget, htarget']
end QEC.Distillation.KT19PrimeQuditCSS
