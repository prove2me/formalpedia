-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.phase_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:42:39.557768+00:00
-- url     : https://prove2.me/submissions/a4fc9657-160a-4f10-b415-6307acab54d2

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
theorem _root_.solution (p : Nat) [NeZero p] {Index : Type u}
    (indices : Finset Index) (f : Index → ZMod p) :
    phase p (∑ index ∈ indices, f index) = ∏ index ∈ indices, phase p (f index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [phase_zero]
  | insert index indices hindex ih =>
      simp only [Finset.sum_insert, hindex, not_false_eq_true, Finset.prod_insert, phase_add, ih]
end QEC.Distillation.KT19PrimeQuditCSS
