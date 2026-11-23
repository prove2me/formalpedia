-- Prove2me | solution 1 for PI.OkpW.pinv_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:27.284269+00:00
-- url     : https://prove2.me/submissions/b967827b-493e-4586-96dc-a4a4d37c66ca

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
theorem _root_.solution : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
end PI.OkpW
