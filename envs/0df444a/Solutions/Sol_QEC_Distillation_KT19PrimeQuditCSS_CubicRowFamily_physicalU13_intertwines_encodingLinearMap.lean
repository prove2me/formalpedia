-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_intertwines_encodingLinearMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:51:00.133144+00:00
-- url     : https://prove2.me/submissions/354ffad9-1bf6-4697-932c-2ebd258bbb47

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_physicalU13_cosetKet

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
    (psi : PrimeQuditRegister p Logical) :
    _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p (R.encodingLinearMap psi) =
    R.encodingLinearMap (R.logicalInverseU13 psi)
    := by
  unfold encodingLinearMap
  change _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p (∑ u : Logical → ZMod p, psi u • R.cosetKet u) =
    ∑ u : Logical → ZMod p, (R.logicalInverseU13 psi) u • R.cosetKet u
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro u _
  rw [map_smul, R.physicalU13_cosetKet, smul_smul]
  change (psi u * R.logicalInverseAmplitude u) • R.cosetKet u =
    (R.logicalInverseAmplitude u * psi u) • R.cosetKet u
  rw [mul_comm]
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
