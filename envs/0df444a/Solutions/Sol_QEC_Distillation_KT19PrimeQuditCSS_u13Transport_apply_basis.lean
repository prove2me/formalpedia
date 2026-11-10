-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.u13Transport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:42:48.544249+00:00
-- url     : https://prove2.me/submissions/f92fc948-1bff-4059-aa19-b144fb76ffca

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
    u13Transport p (quditBasisKet p x) =
      u13Amplitude p x • quditBasisKet p x := by
  classical
  ext label
  by_cases hlabel : label = x
  · subst label
    simp [u13Transport_apply, quditBasisKet, EuclideanSpace.basisFun_apply]
  · simp [u13Transport_apply, quditBasisKet, EuclideanSpace.basisFun_apply, hlabel]
end QEC.Distillation.KT19PrimeQuditCSS
