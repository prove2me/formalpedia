-- Prove2me | solution 1 for PI.JetsPhW.Inv.X_mem_serS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:06.87658+00:00
-- url     : https://prove2.me/submissions/8a9896f1-4d58-4b17-92e0-b6bdd5f572eb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.JetsPhW PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]
namespace PI.JetsPhW.Inv
theorem _root_.solution (S : Subring ℂ_[p]) : (PowerSeries.X : PowerSeries ℂ_[p]) ∈ serS S := by
  intro n
  rw [PowerSeries.coeff_X]
  split_ifs
  · exact S.one_mem
  · exact S.zero_mem
end PI.JetsPhW.Inv
