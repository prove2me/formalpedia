-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_powMonomial_isMultiHomog_630b1c158ab9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:44:49.254815+00:00
-- url     : https://prove2.me/submissions/033e6aed-04ec-48bc-98aa-6e7cdafa0de4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport

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
universe u
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial (R := R) e i) e := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  have key : (∑ k, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [key] at h
  exact h
end GroundTheory.Heights₂.Heights.NumbersDVR
