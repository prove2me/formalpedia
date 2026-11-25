-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_isHomogeneous_of_multiHomog_9ab68c09e1f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:05:17.325005+00:00
-- url     : https://prove2.me/submissions/f468c2f2-28e4-458b-9f13-2f58a8df7c1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_component_lex_mem_d13b7ad741bd

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance 2000] lexDecEq
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (lexGrading ι F) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ m, g = weightedHomogeneousComponent (lexWeight (ι := ι)) m f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (lexWeight (ι := ι)) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨f, hf, m, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, m, rfl⟩
      exact component_lex_mem hI hf m
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, m, rfl⟩ := hx
  exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩
end GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
