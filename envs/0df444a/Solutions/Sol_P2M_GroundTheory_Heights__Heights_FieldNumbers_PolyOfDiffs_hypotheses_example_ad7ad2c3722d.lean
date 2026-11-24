-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PolyOfDiffs_hypotheses_example_ad7ad2c3722d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:19.277221+00:00
-- url     : https://prove2.me/submissions/8440ea24-d217-44e3-a0a0-6513825216ed

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples

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
namespace PolyOfDiffs
theorem _root_.solution :
    ∀ k : Unit, ∃ q : MvPolynomial Unit ℚ, (q = 0 ∨ q.totalDegree < 1) ∧
      EventuallyPoly (diffStep (Pi.single k 1) (fun m : Unit → ℤ => m ())) q := by
  rintro ⟨⟩
  refine ⟨1, Or.inr (by simp), Filter.Eventually.of_forall fun m => ?_⟩
  simp [diffStep]
end PolyOfDiffs
end GroundTheory.Heights₂.Heights.FieldNumbers
