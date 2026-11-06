-- Prove2me | solution 1 for QEC.Semantics.spectralSign_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:37:35.772711+00:00
-- url     : https://prove2.me/submissions/9e300e4e-0246-408c-9a1b-9303e856fbe2

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Definitions.Def_QEC_Semantics_Core_OperatorTraceNorm
import Theorems.Thm_QEC_Semantics_parts_range_isOrtho
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_apply
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjDensity_toOperator
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_apply
attribute [local simp] QEC.Semantics.UnitaryTransport.conjDensity_toOperator



set_option autoImplicit false
universe u
open QEC
open QEC.Semantics
open scoped BigOperators ComplexOrder
noncomputable section
variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
namespace QEC.Semantics
theorem _root_.solution (A : Operator H) : ‖spectralSign A‖ ≤ 1 := by
  let P := positiveSupportProjection A
  let N := negativeSupportProjection A
  have hP : IsStarProjection P := isStarProjection_starProjection
  have hN : IsStarProjection N := isStarProjection_starProjection
  have hPN : P * N = 0 := by
    exact (parts_range_isOrtho A).starProjection_comp_starProjection
  have hNP : N * P = 0 := by
    exact (parts_range_isOrtho A).symm.starProjection_comp_starProjection
  have hsum : IsStarProjection (P + N) := hP.add hN hPN
  have hsquare : star (P - N) * (P - N) = P + N := by
    rw [star_sub, hP.isSelfAdjoint.star_eq, hN.isSelfAdjoint.star_eq]
    simp only [sub_mul, mul_sub, hP.isIdempotentElem.eq,
      hN.isIdempotentElem.eq, hPN, hNP, sub_zero, zero_sub, sub_neg_eq_add]
  have hsq : ‖P - N‖ * ‖P - N‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, hsquare]
    exact hsum.norm_le _
  change ‖P - N‖ ≤ 1
  nlinarith [norm_nonneg (P - N)]
end QEC.Semantics
