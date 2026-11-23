-- Prove2me | solution 1 for PI.FglShared.coeff_logS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:25.120537+00:00
-- url     : https://prove2.me/submissions/ef3b2d36-ddab-4a68-b5d7-6dc3d3b19ea0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_ExpCongruenceExtendsToSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupCommon_ExpLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.FglShared
open MvPowerSeries
variable {p : ℕ} [Fact p.Prime]
namespace PI.FglShared
theorem _root_.solution {σ : Type} (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (logS F) = ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
      if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * coeff α ((F - 1) ^ n) / (n : ℂ_[p]) :=
  rfl
end PI.FglShared
