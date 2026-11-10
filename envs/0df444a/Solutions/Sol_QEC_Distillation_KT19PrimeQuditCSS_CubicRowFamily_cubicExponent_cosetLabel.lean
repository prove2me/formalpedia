-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cubicExponent_cosetLabel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:47:00.793069+00:00
-- url     : https://prove2.me/submissions/cc8236a0-c6bf-4766-bd99-3b9ea31c0715

import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Definitions.Def_QEC_Distillation_PrimeQuditProtocol_CubicCSS
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_cubicExponent_eq_cubicPairing
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cosetLabel_eq_combinedWord
import Theorems.Thm_QEC_Distillation_KT19PrimeQuditCSS_CubicRowFamily_cubicPairing_combinedWord_eq_diagonal
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
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    cubicExponent p (R.cosetLabel u h) =
      -(∑ a : Logical, u a ^ 3 * R.epsilon a) := by
  rw [cubicExponent_eq_cubicPairing, R.cosetLabel_eq_combinedWord,
    R.cubicPairing_combinedWord_eq_diagonal]
  calc
    (∑ a : Logical, combinedCoefficient u h (Sum.inl a) ^ 3 * R.epsilon a) =
        ∑ a : Logical, -(u a ^ 3 * R.epsilon a) := by
      apply Finset.sum_congr rfl
      intro a _
      simp only [combinedCoefficient]
      ring
    _ = -(∑ a : Logical, u a ^ 3 * R.epsilon a) := by
      rw [Finset.sum_neg_distrib]
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
