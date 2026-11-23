-- Prove2me | solution 1 for PI.OkpW.tau_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:16.835435+00:00
-- url     : https://prove2.me/submissions/eb0f6ba8-dee5-420d-882c-8a756624d359

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
theorem _root_.solution (τ : K →+* ℂ_[p]) (x : 𝓞 K) (n : ℕ) : τ ((x ^ n : 𝓞 K) : K) = τ (x : K) ^ n := by
  simp [map_pow]
end PI.OkpW
