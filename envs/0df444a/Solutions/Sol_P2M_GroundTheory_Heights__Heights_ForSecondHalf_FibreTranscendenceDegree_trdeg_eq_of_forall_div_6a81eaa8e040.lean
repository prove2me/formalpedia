-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_trdeg_eq_of_forall_div_6a81eaa8e040
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:49:50.254151+00:00
-- url     : https://prove2.me/submissions/efab8be5-8ae3-4713-9cc1-a70ed6a34651

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MixedFieldContraction_ContractMixedFieldStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PIntDomainDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PEvalKerKrullDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PFibreMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_SemipositiveHeights_FibreDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ForSecondHalf_FibreTranscendenceDegree_isAlgebraic_of_forall_div_b61d5af56ab3
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
    (hZ : Function.Injective (algebraMap ℤ M))
    (h : ∀ m : M, ∃ a b : M, a ∈ B ∧ b ∈ B ∧ b ≠ 0 ∧ m = a / b) :
    Algebra.trdeg ℤ M = Algebra.trdeg ℤ B := by
  have := isAlgebraic_of_forall_div B h
  have : FaithfulSMul ℤ B := (faithfulSMul_iff_algebraMap_injective ℤ B).mpr fun a b hab =>
    hZ (by simpa using congrArg Subtype.val hab)
  have : FaithfulSMul B M := (faithfulSMul_iff_algebraMap_injective B M).mpr Subtype.val_injective
  have h0 := trdeg_add_eq ℤ B (A := M)
  rw [trdeg_eq_zero (R := B) (A := M), add_zero] at h0
  exact h0.symm
end GroundTheory.Heights₂.Heights.ForSecondHalf.FibreTranscendenceDegree
