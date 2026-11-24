-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_separator_d6cdd5665e0a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:01.426281+00:00
-- url     : https://prove2.me/submissions/136b82a2-6945-43eb-b9d6-d650ed321f13

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_form_mem_not_mem_9fb2fa7ea052

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
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {H : Ideal (MRing ι R)} [hH : H.IsPrime]
    (S : Finset (Ideal (MRing ι R))) (hS : ∀ H' ∈ S, IsMultiHomogIdeal H' ∧ ¬ H' ≤ H) :
    ∃ (a : MRing ι R) (A : K → ℕ), IsMultiHomog a A ∧ a ∉ H ∧ ∀ H' ∈ S, a ∈ H' := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨1, 0, isWeightedHomogeneous_one _ _, (Ideal.ne_top_iff_one H).mp hH.ne_top, by simp⟩
  | @insert H₀ S _ ih =>
    obtain ⟨a, A, ha, haH, haS⟩ := ih fun H' h => hS H' (Finset.mem_insert_of_mem h)
    have h₀ := hS H₀ (Finset.mem_insert_self _ _)
    obtain ⟨x, e, hx, hxH₀, hxH⟩ := exists_form_mem_not_mem h₀.1 h₀.2
    refine ⟨x * a, e + A, hx.mul ha, fun hm => (hH.mem_or_mem hm).elim hxH haH, ?_⟩
    intro H' hH'
    rcases Finset.mem_insert.mp hH' with rfl | h
    · exact Ideal.mul_mem_right _ _ hxH₀
    · exact Ideal.mul_mem_left _ _ (haS H' h)
end GroundTheory.Heights₂.Heights.NumbersDVR
