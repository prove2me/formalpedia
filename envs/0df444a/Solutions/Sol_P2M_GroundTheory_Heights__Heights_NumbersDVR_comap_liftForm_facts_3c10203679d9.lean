-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_comap_liftForm_facts_3c10203679d9
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:55:42.46953+00:00
-- url     : https://prove2.me/submissions/e8bccc8c-0701-4d4b-b0b6-709103ef8413

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LiftFormNotMemBlowUpOf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_X_709b97b21fde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_liftForm_mem_blowUpOf_d5667072f554

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
variable {J : Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {P : Ideal (MRing ι R)} {u : J → MRing ι R}
    {W : Ideal (MRing (extIdx ι J) R)} (hW : W.IsPrime) (hQW : blowUpOf P u ≤ W) (hrel : IsRelevant W) :
    (W.comap (liftForm (J := J))).IsPrime ∧ P ≤ W.comap (liftForm (J := J)) ∧
      IsRelevant (W.comap (liftForm (J := J))) ∧ ∃ j, (newVar j : MRing (extIdx ι J) R) ∉ W := by
  refine ⟨Ideal.comap_isPrime _ _, fun p hp => hQW (liftForm_mem_blowUpOf hp), fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hrel (some k)
    exact ⟨i, by rw [Ideal.mem_comap, liftForm_X]; exact hi⟩
  · obtain ⟨j, hj⟩ := hrel none
    exact ⟨j, hj⟩
end GroundTheory.Heights₂.Heights.NumbersDVR
