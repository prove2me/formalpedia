-- Prove2me | solution 1 for QEC.Semantics.clbtGeneratorBlockTwo_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:06:45.83841+00:00
-- url     : https://prove2.me/submissions/3f9f1e98-7942-4784-b163-b7a3f6cfe04d

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_selfAdjointTraceNormOneToOne_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_apply_le_selfAdjointTraceNormOneToOne
import Theorems.Thm_QEC_Semantics_clbtGeneratorBlockTwo_eq_negative_tail
import Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_projectedTail_eq_complementTrace
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_operatorNorm_nonneg
import Theorems.Thm_QEC_Semantics_operatorNorm_projection_le
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_projectedTail_positive
import Theorems.Thm_QEC_Semantics_re_trace_complement_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
import Theorems.Thm_QEC_Semantics_traceNorm_mul_right_le
import Theorems.Thm_QEC_Semantics_traceNorm_neg
import Theorems.Thm_QEC_Semantics_traceNorm_nonneg
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
private theorem commute_one_sub_right {A P : Operator H} (h : Commute A P) :
    Commute A (1 - P) := by
  rw [Commute]
  change A * (1 - P) = (1 - P) * A
  rw [mul_sub, sub_mul, h.eq]
  simp
private theorem traceNorm_mul_projection_le
    (P A : Operator H) (hP : IsStarProjection P) :
    traceNorm (P * A) ≤ traceNorm A := by
  calc
    traceNorm (P * A) ≤ operatorNorm P * traceNorm A :=
      traceNorm_mul_left_le P A
    _ ≤ 1 * traceNorm A :=
      mul_le_mul_of_nonneg_right (operatorNorm_projection_le P hP)
        (traceNorm_nonneg A)
    _ = traceNorm A := one_mul _
private theorem traceNorm_mul_complement_le
    (P A : Operator H) (hP : IsStarProjection P) :
    traceNorm ((1 - P) * A) ≤ traceNorm A :=
  traceNorm_mul_projection_le (1 - P) A hP.one_sub
private theorem projectedTail_eq_complement_mul_of_commute
    (P A : Operator H) (hP : IsStarProjection P) (hPA : Commute P A) :
    projectedTail P A = (1 - P) * A := by
  rw [projectedTail]
  have hQ : Commute (1 - P) A := commute_one_sub_right hPA.symm |>.symm
  calc
    (1 - P) * A * (1 - P) = (1 - P) * (A * (1 - P)) := mul_assoc _ _ _
    _ = (1 - P) * ((1 - P) * A) := by rw [hQ.eq.symm]
    _ = ((1 - P) * (1 - P)) * A := (mul_assoc _ _ _).symm
    _ = (1 - P) * A := by rw [hP.one_sub.isIdempotentElem.eq]
private theorem traceNorm_complement_mul_density_eq_badMass [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H)
    (hPrho : Commute P rho.toOperator) :
    traceNorm ((1 - P) * rho.toOperator) =
      Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator)) := by
  calc
    traceNorm ((1 - P) * rho.toOperator) =
        traceNorm (projectedTail P rho.toOperator) := by
      rw [projectedTail_eq_complement_mul_of_commute P rho.toOperator hP hPrho]
    _ = Complex.re (LinearMap.trace ℂ H ((1 - P) * rho.toOperator)) :=
      rho.traceNorm_projectedTail_eq_complementTrace P hP
private theorem tail_symmetric
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H)
    (hPrho : Commute P rho.toOperator) :
    ((1 - P) * rho.toOperator).IsSymmetric := by
  rw [← projectedTail_eq_complement_mul_of_commute P rho.toOperator hP hPrho]
  exact (projectedTail_positive P rho.toOperator hP rho.positive).isSymmetric
private theorem clbtGibbsTailMass_nonneg [Nontrivial H]
    (P : Operator H) (hP : IsStarProjection P) (rho : DensityOperator H) :
    0 ≤ clbtGibbsTailMass P rho :=
  re_trace_complement_nonneg P rho.toOperator hP rho.positive
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
theorem _root_.solution [Fintype ι] [Nontrivial H]
    (J : ι → Operator H) (O P : Operator H) (rho : DensityOperator H)
    (hprotected : JumpProtected J O P) (hO : O.IsSymmetric)
    (hP : IsStarProjection P) (hOP : Commute O P)
    (hOrho : Commute O rho.toOperator) (hPrho : Commute P rho.toOperator)
    (hstationary : lindbladDissipator J rho.toOperator = 0)
    (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockTwo (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  have hTsym : T.IsSymmetric := tail_symmetric P hP rho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  rw [clbtGeneratorBlockTwo_eq_negative_tail J O P rho hprotected hO hP hOP
    hOrho hPrho hstationary, traceNorm_neg]
  calc
    traceNorm ((1 - P) * lindbladDissipator J T * O) ≤
        operatorNorm O * traceNorm ((1 - P) * lindbladDissipator J T) :=
      traceNorm_mul_right_le ((1 - P) * lindbladDissipator J T) O
    _ ≤ operatorNorm O * traceNorm (lindbladDissipator J T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_mul_complement_le P (lindbladDissipator J T) hP)
        (operatorNorm_nonneg O)
    _ ≤ operatorNorm O *
        (lindbladDissipatorNorm J * traceNorm T) :=
      mul_le_mul_of_nonneg_left
        (traceNorm_apply_le_selfAdjointTraceNormOneToOne
          (lindbladDissipator J) T hTsym)
        (operatorNorm_nonneg O)
    _ = operatorNorm O *
        (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ 2 * (lindbladDissipatorNorm J * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_right hOnorm (mul_nonneg hLnonneg hmass)
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring
end QEC.Semantics
