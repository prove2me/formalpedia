-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_eventualValue_eq_zero_9297a58f17ee
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:53:39.993551+00:00
-- url     : https://prove2.me/submissions/3f147a1f-3bd7-4664-9d2c-bfd55d57052b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted

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
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {K : Type*} {f : (K → ℤ) → ℤ}
    (h : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  unfold eventualValue
  split_ifs with hc
  · obtain ⟨m, h1, h2⟩ := (hc.choose_spec.and h).exists
    rw [← h1, h2]
  · rfl
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
