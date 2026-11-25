-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_isRelevant_map_c55c7df7a8e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:28:51.657249+00:00
-- url     : https://prove2.me/submissions/5b3575b1-18be-47dc-aaed-8c5ba3634b96

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumBaseChange
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_mem_of_map_mem_a8a861175ce6

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
variable {σ : Type*} {F : Type*} [Field F] {F' : Type*} [Field F'] [Algebra F F']
variable {K : Type*} {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {I : Ideal (MRing ι F)} (hI : IsRelevant I) :
    IsRelevant (I.map (map (algebraMap F F'))) := by
  intro k
  obtain ⟨i, hi⟩ := hI k
  refine ⟨i, fun h => hi (mem_of_map_mem (F' := F') ?_)⟩
  rwa [map_X]
end GroundTheory.Heights₂.Heights.FieldNumbers
