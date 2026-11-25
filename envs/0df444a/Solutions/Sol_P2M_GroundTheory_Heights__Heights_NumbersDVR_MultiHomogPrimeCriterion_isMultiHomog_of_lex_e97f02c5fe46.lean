-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_isMultiHomog_of_lex_e97f02c5fe46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:10.025156+00:00
-- url     : https://prove2.me/submissions/d6872316-7aa8-4419-9cde-5e3f58df55f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_injective_d0613a591d1a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_lexDeg_surjective_74d3e094c6c3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_weight_lexDeg_0fa8b812e0c3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
theorem _root_.solution {x : MRing ι R} {i : Lex (Fin (Fintype.card K) → ℕ)}
    (hx : IsWeightedHomogeneous (lexDeg ∘ blockWeight ι) x i) : ∃ s, IsMultiHomog x s := by
  obtain ⟨b, rfl⟩ := lexDeg_surjective i
  refine ⟨b, fun d hd => ?_⟩
  have h := hx hd
  rw [weight_lexDeg] at h
  exact lexDeg_injective h
end GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
