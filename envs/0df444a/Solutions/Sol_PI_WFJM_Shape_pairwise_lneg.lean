-- Prove2me | solution 1 for PI.WFJM.Shape.pairwise_lneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:44.475471+00:00
-- url     : https://prove2.me/submissions/a57ae116-689d-41e2-8a61-006e3da2a4aa

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lneg α).Pairwise (· ≥ ·) := by
  unfold lneg
  rw [List.pairwise_reverse, List.pairwise_ofFn]
  intro i j hij
  have : α j ≤ α i := h hij.le
  simp only [ge_iff_le, neg_le_neg_iff]
  exact_mod_cast this
end PI.WFJM.Shape
