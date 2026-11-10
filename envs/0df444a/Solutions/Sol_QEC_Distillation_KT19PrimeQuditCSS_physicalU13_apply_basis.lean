-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.physicalU13_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:45:04.745623+00:00
-- url     : https://prove2.me/submissions/a74155f0-f952-4c59-b75c-0a92300dda2a

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply
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
attribute [local instance] primeQuditRegisterLabelFintype
namespace QEC.Distillation.KT19PrimeQuditCSS
theorem _root_.solution (p : Nat) [NeZero p] {Site : Type u}
    [Fintype Site] [DecidableEq Site] (label : PrimeQuditRegisterLabel p Site) :
    physicalU13 p (registerBasisKet p label) =
      (∏ site : Site, u13AtAmplitude p site label) • registerBasisKet p label := by
  classical
  ext target
  by_cases htarget : target = label
  · subst target
    simp [physicalU13_apply, registerBasisKet, EuclideanSpace.basisFun_apply]
  · simp [physicalU13_apply, registerBasisKet, EuclideanSpace.basisFun_apply, htarget]
end QEC.Distillation.KT19PrimeQuditCSS
