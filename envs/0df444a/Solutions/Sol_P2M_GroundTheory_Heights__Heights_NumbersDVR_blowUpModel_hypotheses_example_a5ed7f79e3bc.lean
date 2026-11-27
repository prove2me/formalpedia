-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_blowUpModel_hypotheses_example_a5ed7f79e3bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:30.689585+00:00
-- url     : https://prove2.me/submissions/33c05466-70c3-4366-80bd-0d23ae86661b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_SpanTwoIsPrimeRelevant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lemmas_hypotheses_example_719c75c092f9


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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution :
    let S := MRing (fun _ : Unit => Fin 2) ℤ_[2]
    IsModelOver (⊥ : Ideal S) 1 ∧ (∀ j : Fin 2, IsMultiHomog (X ⟨(), j⟩ : S) (Pi.single () 1)) ∧
      ∃ j : Fin 2, (X ⟨(), j⟩ : S) ∉ (⊥ : Ideal S) := by
  intro S
  obtain ⟨hmodel, hX0, -⟩ := lemmas_hypotheses_example
  exact ⟨hmodel, fun j => isWeightedHomogeneous_X _ _ _, 0, hX0⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
