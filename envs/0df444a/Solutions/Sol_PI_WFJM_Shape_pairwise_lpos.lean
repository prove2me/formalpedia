-- Prove2me | solution 1 for PI.WFJM.Shape.pairwise_lpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:48.219696+00:00
-- url     : https://prove2.me/submissions/48c05aec-9056-4e8c-8dd5-83c17ac916e1

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
theorem _root_.solution {m : ℕ} {α : Fin m → ℕ} (h : Antitone α) : (lpos α).Pairwise (· ≥ ·) := by
  unfold lpos
  rw [List.pairwise_ofFn]
  intro i j hij
  exact_mod_cast h hij.le
end PI.WFJM.Shape
