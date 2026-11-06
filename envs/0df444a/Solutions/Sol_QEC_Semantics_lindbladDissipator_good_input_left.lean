-- Prove2me | solution 1 for QEC.Semantics.lindbladDissipator_good_input_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:02.511508+00:00
-- url     : https://prove2.me/submissions/d0d721a1-538d-49ac-a580-c4b07d892e8e

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_JumpProtected_jump_mul_observable_projector
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
private theorem jumpTerm_good_input_left [Fintype ι]
    (J : ι → Operator H) (O P A : Operator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P) (a : ι) :
    P * lindbladJumpTerm (J a) (O * P * A) =
      O * P * lindbladJumpTerm (J a) (P * A) := by
  have hj := hprotected.jump_mul_observable_projector a
  have hjadj := hprotected.projector_mul_observable_adjoint hO hP a
  have hgain :
      P * (J a * (O * P * A) * LinearMap.adjoint (J a)) =
        O * P * (J a * (P * A) * LinearMap.adjoint (J a)) := by
    calc
      _ = P * ((J a * O * P) * A * LinearMap.adjoint (J a)) := by
        noncomm_ring
      _ = P * ((O * J a * P) * A * LinearMap.adjoint (J a)) := by rw [hj]
      _ = _ := by noncomm_ring [hOP.eq]
  have hlossLeft :
      P * ((LinearMap.adjoint (J a) * J a) * (O * P * A)) =
        O * P * ((LinearMap.adjoint (J a) * J a) * (P * A)) := by
    calc
      _ = P * LinearMap.adjoint (J a) * (J a * O * P) * A := by
        simp only [mul_assoc]
      _ = P * LinearMap.adjoint (J a) * (O * J a * P) * A := by rw [hj]
      _ = (P * LinearMap.adjoint (J a) * O) * J a * P * A := by
        simp only [mul_assoc]
      _ = (P * O * LinearMap.adjoint (J a)) * J a * P * A := by rw [hjadj]
      _ = O * P * LinearMap.adjoint (J a) * J a * P * A := by
        exact congrArg (fun X : Operator H => X * LinearMap.adjoint (J a) *
          J a * P * A) hOP.eq.symm
      _ = _ := by simp only [mul_assoc]
  have hlossRight :
      P * ((O * P * A) * (LinearMap.adjoint (J a) * J a)) =
        O * P * ((P * A) * (LinearMap.adjoint (J a) * J a)) := by
    calc
      _ = P * O * P * A * (LinearMap.adjoint (J a) * J a) := by
        simp only [mul_assoc]
      _ = O * P * P * A * (LinearMap.adjoint (J a) * J a) := by
        exact congrArg (fun X : Operator H => X * P * A *
          (LinearMap.adjoint (J a) * J a)) hOP.eq.symm
      _ = _ := by simp only [mul_assoc]
  rw [lindbladJumpTerm_apply, lindbladJumpTerm_apply]
  simp only [mul_sub, mul_add, mul_smul_comm]
  rw [hgain, hlossLeft, hlossRight]
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
    (hP : IsStarProjection P) (hOP : Commute O P) :
    P * lindbladDissipator J (O * P * A) =
      O * P * lindbladDissipator J (P * A) := by
  rw [lindbladDissipator_apply, lindbladDissipator_apply, Finset.mul_sum,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  exact jumpTerm_good_input_left J O P A hprotected hO hP hOP a
end QEC.Semantics
