-- Prove2me | solution 1 for PI.OkpW.dvd_pow_q_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:16.557795+00:00
-- url     : https://prove2.me/submissions/89f10c8f-6d4e-460b-8464-360e8ba231e0

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
theorem _root_.solution (a b : 𝓞 K) (h : (p : 𝓞 K) ∣ a - b) (k : ℕ) :
    (p : 𝓞 K) ^ (k + 1) ∣ a ^ ((p ^ 2) ^ k) - b ^ ((p ^ 2) ^ k) := by
  have h1 := dvd_sub_pow_of_dvd_sub h (2 * k)
  rw [show (p ^ 2) ^ k = p ^ (2 * k) by rw [← pow_mul]]
  exact (pow_dvd_pow _ (by omega)).trans h1
end PI.OkpW
