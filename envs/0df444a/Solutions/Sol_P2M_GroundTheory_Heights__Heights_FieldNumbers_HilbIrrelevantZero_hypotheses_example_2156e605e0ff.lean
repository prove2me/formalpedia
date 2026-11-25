-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbIrrelevantZero_hypotheses_example_2156e605e0ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:22.718387+00:00
-- url     : https://prove2.me/submissions/8ba3d0d4-f000-488a-975b-d8255c031511

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound

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
namespace GroundTheory.Heights₂.Heights.FieldNumbers
namespace HilbIrrelevantZero
theorem _root_.solution :
    ¬ IsRelevant (Ideal.span (Set.range X) : Ideal (MRing (ProjIdx 1) ℚ)) := by
  intro h
  obtain ⟨i, hi⟩ := h ()
  exact hi (Ideal.subset_span ⟨_, rfl⟩)
end HilbIrrelevantZero
end GroundTheory.Heights₂.Heights.FieldNumbers
