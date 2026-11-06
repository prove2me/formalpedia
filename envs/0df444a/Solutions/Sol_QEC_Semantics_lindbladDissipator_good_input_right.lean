-- Prove2me | solution 1 for QEC.Semantics.lindbladDissipator_good_input_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:04.644646+00:00
-- url     : https://prove2.me/submissions/53cc71a3-d925-459d-b79b-99c5cf508788

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_JumpProtected_projector_mul_observable_adjoint
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_traceNorm_neg
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.id_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator
attribute [local simp] QEC.Semantics.finiteLindbladEvolutionLinearMap_zero
attribute [local simp] QEC.Semantics.partialTraceRightRaw_cptp_toLinearMap
attribute [local simp] QEC.Semantics.partialTraceRightRaw_mapDensity_toOperator
attribute [local simp] QEC.Semantics.traceNorm_neg


section
universe u v
namespace QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
private theorem jumpTerm_good_input_right [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPA : Commute P A) (hOA : Commute O A) (a : ι) :
    (1 - P) * lindbladJumpTerm (J a) (O * P * A) =
      (1 - P) * lindbladJumpTerm (J a) (P * A) * O := by
  have hjadj := hprotected.projector_mul_observable_adjoint hO hP a
  have hOPA : O * P * A = P * A * O := by
    calc
      O * P * A = P * O * A := congrArg (fun X : Operator H => X * A) hOP.eq
      _ = P * (O * A) := mul_assoc _ _ _
      _ = P * (A * O) := by rw [hOA.eq]
      _ = P * A * O := (mul_assoc _ _ _).symm
  have hOPA' : O * (P * A) = P * (A * O) := by
    simpa only [mul_assoc] using hOPA
  have hPAOJ : P * A * O * LinearMap.adjoint (J a) =
      P * A * LinearMap.adjoint (J a) * O := by
    calc
      _ = A * P * O * LinearMap.adjoint (J a) := by
        exact congrArg (fun X : Operator H => X * O * LinearMap.adjoint (J a)) hPA.eq
      _ = A * (P * O * LinearMap.adjoint (J a)) := by simp only [mul_assoc]
      _ = A * (P * LinearMap.adjoint (J a) * O) := by rw [hjadj]
      _ = A * P * LinearMap.adjoint (J a) * O := by simp only [mul_assoc]
      _ = P * A * LinearMap.adjoint (J a) * O := by
        exact congrArg (fun X : Operator H => X * LinearMap.adjoint (J a) * O)
          hPA.eq.symm
  have hOPAJ : O * (P * (A * LinearMap.adjoint (J a))) =
      P * (A * (LinearMap.adjoint (J a) * O)) := by
    calc
      _ = (O * P * A) * LinearMap.adjoint (J a) := by simp only [mul_assoc]
      _ = (P * A * O) * LinearMap.adjoint (J a) := by rw [hOPA]
      _ = P * A * LinearMap.adjoint (J a) * O := hPAOJ
      _ = _ := by simp only [mul_assoc]
  have hQP : (1 - P) * P = 0 := by
    rw [sub_mul, one_mul, hP.isIdempotentElem.eq, sub_self]
  have hgain :
      (1 - P) * (J a * (O * P * A) * LinearMap.adjoint (J a)) =
        (1 - P) * (J a * (P * A) * LinearMap.adjoint (J a)) * O := by
    simp only [mul_assoc]
    rw [hOPAJ]
  have hlossLeft :
      (1 - P) * ((LinearMap.adjoint (J a) * J a) * (O * P * A)) =
        (1 - P) * ((LinearMap.adjoint (J a) * J a) * (P * A)) * O := by
    simp only [mul_assoc]
    rw [hOPA']
  have hlossRightLeft :
      (1 - P) * ((O * P * A) * (LinearMap.adjoint (J a) * J a)) = 0 := by
    calc
      _ = (1 - P) * ((O * P) * (A * (LinearMap.adjoint (J a) * J a))) := by
        simp only [mul_assoc]
      _ = (1 - P) * ((P * O) * (A * (LinearMap.adjoint (J a) * J a))) := by
        rw [hOP.eq]
      _ = ((1 - P) * P) * (O * (A * (LinearMap.adjoint (J a) * J a))) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hQP, zero_mul]
  have hlossRightBase :
      (1 - P) * ((P * A) * (LinearMap.adjoint (J a) * J a)) = 0 := by
    calc
      _ = ((1 - P) * P) * (A * (LinearMap.adjoint (J a) * J a)) := by
        simp only [mul_assoc]
      _ = 0 := by rw [hQP, zero_mul]
  have hlossRightRight :
      (1 - P) * ((P * A) * (LinearMap.adjoint (J a) * J a)) * O = 0 := by
    rw [hlossRightBase, zero_mul]
  rw [lindbladJumpTerm_apply, lindbladJumpTerm_apply]
  simp only [mul_sub, mul_add, mul_smul_comm]
  rw [hgain, hlossLeft, hlossRightLeft]
  simp only [add_zero, hlossRightBase]
  conv_rhs => rw [sub_mul, smul_mul_assoc]
end
end QEC.Semantics
end

set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hPA : Commute P A) (hOA : Commute O A) :
    (1 - P) * lindbladDissipator J (O * P * A) =
      (1 - P) * lindbladDissipator J (P * A) * O := by
  rw [lindbladDissipator_apply, lindbladDissipator_apply, Finset.mul_sum,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  exact jumpTerm_good_input_right J O P A hprotected hO hP hOP hPA hOA a
end QEC.Semantics
