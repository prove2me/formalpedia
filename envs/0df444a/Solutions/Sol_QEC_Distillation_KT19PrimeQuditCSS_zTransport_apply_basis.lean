-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.zTransport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:44:51.683199+00:00
-- url     : https://prove2.me/submissions/e89e0d32-0a85-420d-ac60-3614b71c27d7

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
    zTransport p (quditBasisKet p x) = zAmplitude p x • quditBasisKet p x := by
  classical
  ext label
  rw [zTransport_apply]
  by_cases hlabel : label = x
  · subst label
    simp [quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]
end QEC.Distillation.KT19PrimeQuditCSS
