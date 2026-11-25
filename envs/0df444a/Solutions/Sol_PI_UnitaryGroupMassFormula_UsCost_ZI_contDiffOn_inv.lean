-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UsCost.ZI.contDiffOn_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:48:38.652052+00:00
-- url     : https://prove2.me/submissions/c6d4b27a-136e-4ac4-82cf-af8ec97c4499

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_ZIterB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.ZI
variable (s : ℕ)
namespace PI.UnitaryGroupMassFormula.UsCost.ZI
theorem _root_.solution (n : ℕ) : ContDiffOn ℝ n (Ring.inverse : En s → En s) {x : En s | IsUnit x} :=
  fun x hx => by
    obtain ⟨u, rfl⟩ := hx
    exact (contDiffAt_ringInverse ℝ u).contDiffWithinAt
end PI.UnitaryGroupMassFormula.UsCost.ZI
