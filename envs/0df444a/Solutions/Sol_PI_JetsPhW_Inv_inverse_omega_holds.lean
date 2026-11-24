-- Prove2me | solution 1 for PI.JetsPhW.Inv.inverse_omega_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:16.797796+00:00
-- url     : https://prove2.me/submissions/f958e2be-efd5-4ffc-b5bc-d13d42bed28d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Theorems.Thm_UpperTheory_Reformulated_B_Gwa1_inverse_omega_holds


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
theorem _root_.solution : InvOmega :=
  _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds
end PI.JetsPhW.Inv
