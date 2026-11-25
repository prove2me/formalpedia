-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_eventualValue_eq_f2e34bf02972
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:20.043187+00:00
-- url     : https://prove2.me/submissions/52899a79-e414-4382-aba0-0c88aa5e2a77

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsAddBlock
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPNProduct

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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR Filter
noncomputable section
universe u
variable {K : Type}
namespace GroundTheory.Heights₂.Heights.FieldNumbers
theorem _root_.solution {f : (Option K → ℤ) → ℤ} {c : ℤ} (hf : ∀ᶠ m in atTop, f m = c) :
    eventualValue f = c := by
  have h : ∃ c, ∀ᶠ m in atTop, f m = c := ⟨c, hf⟩
  unfold eventualValue
  rw [dif_pos h]
  obtain ⟨m, h1, h2⟩ := (h.choose_spec.and hf).exists
  exact h1.symm.trans h2
end GroundTheory.Heights₂.Heights.FieldNumbers
