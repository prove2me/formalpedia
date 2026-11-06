-- Prove2me | solution 1 for QEC.Semantics.clbtGeneratorBlockThree_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:03:05.501074+00:00
-- url     : https://prove2.me/submissions/d8cc1338-2481-4534-b168-875d54157cc0

import Definitions.Def_QEC_Semantics_Dynamics_Lindblad
import Definitions.Def_QEC_Semantics_Dynamics_FourBlockGenerator
import Theorems.Thm_QEC_Semantics_selfAdjointTraceNormOneToOne_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_apply_le_selfAdjointTraceNormOneToOne
import Theorems.Thm_QEC_Semantics_DensityOperator_traceNorm_projectedTail_eq_complementTrace
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
import Theorems.Thm_QEC_Semantics_QuantumChannel_id_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
import Theorems.Thm_QEC_Semantics_finiteLindbladEvolutionLinearMap_zero
import Theorems.Thm_QEC_Semantics_operatorNorm_projection_le
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_cptp_toLinearMap
import Theorems.Thm_QEC_Semantics_partialTraceRightRaw_mapDensity_toOperator
import Theorems.Thm_QEC_Semantics_projectedTail_positive
import Theorems.Thm_QEC_Semantics_re_trace_complement_nonneg
import Theorems.Thm_QEC_Semantics_traceNorm_mul_left_le
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
private theorem observable_tail_symmetric
    (O P : Operator H) (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P)
    (rho : DensityOperator H) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) :
    (O * (1 - P) * rho.toOperator).IsSymmetric := by
  have htailComm : Commute O ((1 - P) * rho.toOperator) :=
    (commute_one_sub_right hOP).mul_right hOrho
  have htailSym : ((1 - P) * rho.toOperator).IsSymmetric :=
    tail_symmetric P hP rho hPrho
  intro x y
  change inner ℂ (O (((1 - P) * rho.toOperator) x)) y =
    inner ℂ x (O (((1 - P) * rho.toOperator) y))
  calc
    inner ℂ (O (((1 - P) * rho.toOperator) x)) y =
        inner ℂ (((1 - P) * rho.toOperator) x) (O y) := hO _ _
    _ = inner ℂ x (((1 - P) * rho.toOperator) (O y)) := htailSym _ _
    _ = inner ℂ x (O (((1 - P) * rho.toOperator) y)) := by
      apply congrArg (inner ℂ x)
      exact LinearMap.congr_fun htailComm.eq.symm y
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
    (hO : O.IsSymmetric) (hP : IsStarProjection P)
    (hOP : Commute O P) (hOrho : Commute O rho.toOperator)
    (hPrho : Commute P rho.toOperator) (hOnorm : operatorNorm O ≤ 2) :
    traceNorm
        (clbtGeneratorBlockThree (lindbladDissipator J) O P rho.toOperator) ≤
      2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by
  let T : Operator H := (1 - P) * rho.toOperator
  let B : Operator H := O * (1 - P) * rho.toOperator
  have hBsym : B.IsSymmetric :=
    observable_tail_symmetric O P hO hP hOP rho hOrho hPrho
  have hTnorm : traceNorm T = clbtGibbsTailMass P rho :=
    traceNorm_complement_mul_density_eq_badMass P hP rho hPrho
  have hBnorm : traceNorm B ≤ operatorNorm O * traceNorm T := by
    simpa only [B, T, mul_assoc] using traceNorm_mul_left_le O T
  have hLnonneg : 0 ≤ lindbladDissipatorNorm J :=
    selfAdjointTraceNormOneToOne_nonneg (lindbladDissipator J)
  have hmass : 0 ≤ clbtGibbsTailMass P rho :=
    clbtGibbsTailMass_nonneg P hP rho
  change traceNorm (P * lindbladDissipator J B) ≤ _
  calc
    traceNorm (P * lindbladDissipator J B) ≤
        traceNorm (lindbladDissipator J B) :=
      traceNorm_mul_projection_le P (lindbladDissipator J B) hP
    _ ≤ lindbladDissipatorNorm J * traceNorm B :=
      traceNorm_apply_le_selfAdjointTraceNormOneToOne
        (lindbladDissipator J) B hBsym
    _ ≤ lindbladDissipatorNorm J * (operatorNorm O * traceNorm T) :=
      mul_le_mul_of_nonneg_left hBnorm hLnonneg
    _ = lindbladDissipatorNorm J *
        (operatorNorm O * clbtGibbsTailMass P rho) := by rw [hTnorm]
    _ ≤ lindbladDissipatorNorm J * (2 * clbtGibbsTailMass P rho) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hOnorm hmass) hLnonneg
    _ = 2 * lindbladDissipatorNorm J * clbtGibbsTailMass P rho := by ring
end QEC.Semantics
