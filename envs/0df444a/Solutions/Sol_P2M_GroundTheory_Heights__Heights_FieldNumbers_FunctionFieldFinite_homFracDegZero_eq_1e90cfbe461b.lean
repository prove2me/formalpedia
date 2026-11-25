-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_homFracDegZero_eq_1e90cfbe461b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:42.756993+00:00
-- url     : https://prove2.me/submissions/26f6cc8d-2885-47d9-b140-6d7216024550

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsFunctionFieldFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsMChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PFunctionFieldFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_FunctionFieldFinite_range_chartMap_599b5829d5e9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
theorem _root_.solution (hD : MChartDehomog.Statement.{u}) (P : Ideal (MRing ι F)) [P.IsPrime]
    (u : ∀ k, ι k) (hu : ∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) :
    homFracDegZero P = IntermediateField.adjoin F (chartGens P u) := by
  apply le_antisymm
  · unfold homFracDegZero
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨b, f, g, hf, hg, -, rfl⟩
    have hm : algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
        (Ideal.Quotient.mk P (chartMonomial u b)) ≠ 0 := by
      rw [chartMonomial, map_prod, map_prod]
      refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
      rw [map_pow, map_pow]
      refine pow_ne_zero _ ?_
      rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
      exact hu k
    have hr : ∀ p, chartMap P u p ∈ IntermediateField.adjoin F (chartGens P u) := fun p =>
      IntermediateField.algebra_adjoin_le_adjoin F _ (by rw [← range_chartMap]; exact ⟨p, rfl⟩)
    have key := div_mem (hr f) (hr g)
    rwa [hD F K ι P u hu f b hf, hD F K ι P u hu g b hg, div_div_div_cancel_right₀ hm] at key
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨v, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨blockWeight ι v, X v, X ⟨v.1, u v.1⟩,
      isWeightedHomogeneous_X _ _ _, isWeightedHomogeneous_X _ _ _, hu v.1, rfl⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.FunctionFieldFinite
