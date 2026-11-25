-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomog_powMonomial_71414389f897
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:38.449104+00:00
-- url     : https://prove2.me/submissions/7fd08857-352a-4e81-8555-cc2ae500b69b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf

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
noncomputable section
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial e i : MRing ι R) e := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  unfold IsMultiHomog powMonomial
  convert h using 1
  funext k
  simp [Finset.sum_apply, blockWeight, Pi.single_apply]
end GroundTheory.Heights₂.Heights.NumbersDVR
