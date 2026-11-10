-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.physicalU13_cosetKet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:49:02.95232+00:00
-- url     : https://prove2.me/submissions/f1244f9b-fa28-439c-be42-d9b6ad673296

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_physicalU13_apply_basis_phase
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicExponent_cosetLabel
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
    _root_.QEC.Distillation.KT19PrimeQuditCSS.physicalU13 p (R.cosetKet u) = R.logicalInverseAmplitude u • R.cosetKet u := by
  unfold cosetKet
  rw [map_smul, map_sum]
  simp_rw [physicalU13_apply_basis_phase, R.cubicExponent_cosetLabel]
  change cosetNormalization p Stabilizer •
      (∑ h : StabilizerLabel p Stabilizer,
        R.logicalInverseAmplitude u • registerBasisKet p (R.cosetLabel u h)) =
      R.logicalInverseAmplitude u •
        (cosetNormalization p Stabilizer •
          ∑ h : StabilizerLabel p Stabilizer, registerBasisKet p (R.cosetLabel u h))
  rw [← Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm]
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
