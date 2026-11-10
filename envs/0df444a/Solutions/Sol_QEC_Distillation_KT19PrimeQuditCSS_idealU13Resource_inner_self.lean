-- Prove2me | solution 1 for QEC.Distillation.KT19PrimeQuditCSS.idealU13Resource_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T10:44:39.181969+00:00
-- url     : https://prove2.me/submissions/c25575df-017a-4f3f-b904-cb6de26fca7f

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
theorem _root_.solution (p : Nat) [NeZero p] :
    inner Complex (idealU13Resource p) (idealU13Resource p) = 1 := by
  rw [idealU13Resource, (u13Transport p).map_inner]
  rw [inner_smul_left, inner_smul_right, inner_sum]
  simp_rw [sum_inner]
  simp only [quditBasisKet, EuclideanSpace.basisFun_apply]
  simp_rw [EuclideanSpace.inner_single_left]
  simp [PiLp.single_apply]
  have hpos : (0 : Real) < (p : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have hsqrt : (Real.sqrt (p : Real) : Complex) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr hpos
  have hsquare :
      (Real.sqrt (p : Real) : Complex) * (Real.sqrt (p : Real) : Complex) =
        (p : Complex) := by
    exact_mod_cast Real.mul_self_sqrt hpos.le
  rw [← hsquare]
  field_simp [hsqrt]
end QEC.Distillation.KT19PrimeQuditCSS
