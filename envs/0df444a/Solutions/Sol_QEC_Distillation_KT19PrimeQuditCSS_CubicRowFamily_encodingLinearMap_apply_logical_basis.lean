-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.encodingLinearMap_apply_logical_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:40.863726+00:00
-- url     : https://prove2.me/submissions/ddcf5dd6-fa12-4803-aa98-6f533d67edd0

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
attribute [local instance] primeQuditRegisterLabelFintype
open QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
variable {p : Nat} [NeZero p] {Logical Stabilizer Site : Type u}
variable [Fintype Logical] [Fintype Stabilizer] [Fintype Site]
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_633
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_634
attribute [local instance] QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily._p2m_local_instance_d01bce0bd8_635
namespace QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
theorem _root_.solution (R : CubicRowFamily p Logical Stabilizer Site)
    (u : Logical → ZMod p) :
    R.encodingLinearMap (registerBasisKet p u) = R.cosetKet u := by
  change (∑ v : Logical → ZMod p, registerBasisKet p u v • R.cosetKet v) = R.cosetKet u
  simp [registerBasisKet, EuclideanSpace.basisFun_apply]
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
