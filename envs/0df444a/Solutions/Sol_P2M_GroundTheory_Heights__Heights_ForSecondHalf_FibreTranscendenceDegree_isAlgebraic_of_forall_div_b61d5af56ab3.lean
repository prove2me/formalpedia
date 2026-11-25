-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:12:06.174041+00:00
-- url     : https://prove2.me/submissions/4ed6aa79-6e3c-4ea3-a5b7-4e7f4caebdff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ForSecondHalf
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
namespace GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
theorem _root_.solution {M : Type} [Field M] (B : Subalgebra ℤ M)
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) : Algebra.IsAlgebraic B M := by
  refine ⟨fun m => ?_⟩
  obtain ⟨a, b, ha, hb, hb0, rfl⟩ := h m
  refine ⟨Polynomial.C (⟨b, hb⟩ : B) * Polynomial.X - Polynomial.C (⟨a, ha⟩ : B), fun h0 => hb0 ?_, ?_⟩
  · have h1 := congrArg (fun p : Polynomial B => p.coeff 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, if_neg one_ne_zero,
      sub_zero, Polynomial.coeff_zero] at h1
    exact congrArg Subtype.val h1
  · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    show b * (a / b) - a = 0
    rw [mul_div_cancel₀ _ hb0, sub_self]
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
