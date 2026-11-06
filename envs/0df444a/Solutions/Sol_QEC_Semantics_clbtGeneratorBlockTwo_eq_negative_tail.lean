-- Prove2me | solution 1 for QEC.Semantics.clbtGeneratorBlockTwo_eq_negative_tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:05:05.613801+00:00
-- url     : https://prove2.me/submissions/0fe7f7f2-b2d8-49bc-8912-4a7a1e1043fd

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_lindbladDissipator_good_input_right
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
private theorem lindbladDissipator_good_input_eq_negative_tail [Fintype ι]
    (J : ι → Operator H) (P : Operator H) (rho : DensityOperator H)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    lindbladDissipator J (P * rho.toOperator) =
      -lindbladDissipator J ((1 - P) * rho.toOperator) := by
  have hrhoSplit :
      rho.toOperator = P * rho.toOperator + (1 - P) * rho.toOperator := by
    noncomm_ring
  have hsum :
      lindbladDissipator J (P * rho.toOperator) +
        lindbladDissipator J ((1 - P) * rho.toOperator) = 0 := by
    rw [← map_add, ← hrhoSplit, hstationary]
  exact eq_neg_of_add_eq_zero_left hsum
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
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0) :
    clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator =
      -((1 - P) * lindbladDissipator J ((1 - P) * rho.toOperator) * O) := by
  rw [clbtGeneratorBlockTwo,
    lindbladDissipator_good_input_right J O P rho.toOperator hprotected hO hP hOP
      hPrho hOrho,
    lindbladDissipator_good_input_eq_negative_tail J P rho hstationary]
  simp
end QEC.Semantics
