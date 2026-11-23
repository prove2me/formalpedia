-- Prove2me | solution 1 for PI.OkpW.tau_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:55.411471+00:00
-- url     : https://prove2.me/submissions/f3a5059a-c4c5-4d28-812b-4078790d4c35

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_CFrob
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_DvdPowQSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
noncomputable section
open PI PI.OkpW
variable {K : Type} [Field K] [NumberField K] {p : ℕ} [hp : Fact p.Prime]
namespace PI.OkpW
theorem _root_.solution (τ : K →+* ℂ_[p]) (x y : 𝓞 K) : τ ((x - y : 𝓞 K) : K) = τ (x : K) - τ (y : K) := by
  simp [map_sub]
end PI.OkpW
