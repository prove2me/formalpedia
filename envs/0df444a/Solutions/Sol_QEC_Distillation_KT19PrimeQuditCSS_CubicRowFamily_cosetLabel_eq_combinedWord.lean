-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily.cosetLabel_eq_combinedWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:43:31.669874+00:00
-- url     : https://prove2.me/submissions/56ca6ea9-b436-4e55-b7ed-00eaf6c73072

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
    (u : Logical → ZMod p) (h : Stabilizer → ZMod p) :
    R.cosetLabel u h = R.combinedWord (combinedCoefficient u h) := by
  classical
  ext site
  simp only [cosetLabel, combinedWord, logicalWord, stabilizerWord,
    Pi.neg_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply,
    combinedCoefficient, row]
  rw [Fintype.sum_sum_type]
  simp
end QEC.Distillation.KT19PrimeQuditCSS.CubicRowFamily
