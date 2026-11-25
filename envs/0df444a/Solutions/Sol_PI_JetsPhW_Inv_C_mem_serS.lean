-- Prove2me | solution 1 for PI.JetsPhW.Inv.C_mem_serS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:47:03.907516+00:00
-- url     : https://prove2.me/submissions/c99bbb4f-58f2-4552-b2c4-3b984c9b6665

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
theorem _root_.solution {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a ∈ serS S := by
  intro n
  rw [PowerSeries.algebraMap_apply]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, PowerSeries.coeff_C]
  split_ifs
  · exact ha
  · exact S.zero_mem
end PI.JetsPhW.Inv
