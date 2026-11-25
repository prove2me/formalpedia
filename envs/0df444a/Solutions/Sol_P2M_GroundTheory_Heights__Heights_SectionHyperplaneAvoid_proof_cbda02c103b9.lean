-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_proof_cbda02c103b9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:49.817586+00:00
-- url     : https://prove2.me/submissions/3573d772-a272-4b12-b2f1-6f46e88969d7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSectionHyperplaneAvoid
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_mem_formSpace_645c641ba987
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_formSpace_ne_top_c7bc28259234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SectionHyperplaneAvoid_isRelevant_of_mem_support_c301370fe534

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
namespace GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
theorem _root_.solution : SectionHyperplaneAvoid.Statement := by
  intro n J u hJ
  let p : Option (divCycle J u).support → Submodule ℂ (Fin n → ℂ) :=
    fun o => o.elim (formSpace J) (fun W => formSpace W.1)
  have hp : ∀ o, p o ≠ ⊤ := by
    rintro (_ | ⟨W, hW⟩)
    · exact formSpace_ne_top hJ.isRelevant
    · exact formSpace_ne_top (isRelevant_of_mem_support hW)
  have hcov : ⋃ o, (p o : Set (Fin n → ℂ)) ≠ Set.univ := fun h =>
    (Subspace.exists_eq_top_of_iUnion_eq_univ h).elim hp
  obtain ⟨ℓ, hℓ⟩ := (Set.ne_univ_iff_exists_notMem _).mp hcov
  simp only [Set.mem_iUnion, not_exists, SetLike.mem_coe] at hℓ
  refine ⟨ℓ, fun h => hℓ none (mem_formSpace.mpr h), fun W hW h => hℓ (some ⟨W, hW⟩) ?_⟩
  exact mem_formSpace.mpr h
end GroundTheory.Heights₂.Heights.SectionHyperplaneAvoid
