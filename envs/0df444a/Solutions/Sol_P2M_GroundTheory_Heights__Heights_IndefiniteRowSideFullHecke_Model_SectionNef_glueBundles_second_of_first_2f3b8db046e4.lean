-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_SectionNef_glueBundles_second_of_first_2f3b8db046e4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:06:33.520901+00:00
-- url     : https://prove2.me/submissions/df8b5445-80b2-4720-88f1-1356023f25f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSectionNef
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GlueBundlesSecondOfFirstAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isRegularSection_form_6765ee38e78f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace SectionNef
theorem _root_.solution (h : _root_.GroundTheory.Heights₂.Heights.Model.SectionNef.Statement) :
    SectionNef.Statement := by
  intro κ _ _ ι _ F _ P hP hd a ha
  have hs : ∃ s : MRing ι F, IsMultiHomog s a ∧ s ∉ P := by
    rcases ha with h1 | h2
    · exact h1
    · exact h2 P hP le_rfl
  obtain ⟨s, hsa, hsP⟩ := hs
  exact h κ ι F P hP hd (fun k => (a k : ℤ)) s 1
    (_root_.GroundTheory.Heights₂.Heights.Model.isRegularSection_form hP.isPrime hsa hsP)
end SectionNef
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
