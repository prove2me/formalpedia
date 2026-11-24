-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_gradedPiece_eq_span_bcb2fa78a226
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:40:04.139247+00:00
-- url     : https://prove2.me/submissions/1e9c13f9-a510-4921-a068-2973db2a707b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange

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
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution (E : Type*) [Field E] (J : Ideal (MRing ι E)) (m : K → ℕ) :
    gradedPiece J m = Submodule.span E ((fun d => Ideal.Quotient.mk J (monomial d (1 : E))) ''
      {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}) := by
  have hspan : weightedHomogeneousSubmodule E (blockWeight ι) m = Submodule.span E
      ((fun d => monomial d (1 : E)) '' {d : (Σ k, ι k) →₀ ℕ | Finsupp.weight (blockWeight ι) d = m}) := by
    apply le_antisymm
    · intro f hf
      rw [mem_weightedHomogeneousSubmodule] at hf
      rw [← f.support_sum_monomial_coeff]
      refine Submodule.sum_mem _ fun d hd => ?_
      have h1 : monomial d (coeff d f) = coeff d f • monomial d (1 : E) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [h1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d, hf (mem_support_iff.mp hd), rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨d, hd, rfl⟩
      exact isWeightedHomogeneous_monomial _ _ _ hd
  unfold gradedPiece
  rw [hspan, Submodule.map_span, Set.image_image]
  rfl
end GroundTheory.Heights₂.Heights.FieldNumbers
