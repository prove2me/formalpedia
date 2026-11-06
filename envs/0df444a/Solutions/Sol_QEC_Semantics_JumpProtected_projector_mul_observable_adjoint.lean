-- Prove2me | solution 1 for QEC.Semantics.JumpProtected.projector_mul_observable_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:52.124205+00:00
-- url     : https://prove2.me/submissions/5e0cee96-51ab-4aff-be44-5cf55e07b2d2

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
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



set_option autoImplicit false
universe u v
open QEC QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u} {ι : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteQuantumSystem H]
namespace QEC.Semantics
namespace JumpProtected
theorem _root_.solution [Fintype ι]
    {J : ι → Operator H} {O P : Operator H} (h : JumpProtected J O P)
    (hO : O.IsSymmetric) (hP : IsStarProjection P) (a : ι) :
    P * O * LinearMap.adjoint (J a) =
      P * LinearMap.adjoint (J a) * O := by
  have hPsym : P.IsSymmetric :=
    (LinearMap.isStarProjection_iff_isSymmetricProjection.mp hP).2
  have ha := congrArg LinearMap.adjoint (h a)
  simp only [Module.End.mul_eq_comp, LinearMap.adjoint_comp, map_sub, map_zero,
    hO.adjoint_eq, hPsym.adjoint_eq] at ha
  change P * (O * LinearMap.adjoint (J a) -
    LinearMap.adjoint (J a) * O) = 0 at ha
  rw [mul_sub] at ha
  exact sub_eq_zero.mp ha
end JumpProtected
end QEC.Semantics
