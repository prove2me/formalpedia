-- Prove2me | solution 1 for PI.OkpW.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:33.304138+00:00
-- url     : https://prove2.me/submissions/21cb1001-6c84-4c52-9980-492ba9154e38

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Theorems.Thm_PI_OkpW_natCard_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open PI PI.OkpW
variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
namespace PI.OkpW
theorem _root_.solution (hK : Module.finrank ℚ K = 2) : Finite (𝓞 K ⧸ Ideal.span {(p : 𝓞 K)}) :=
  Nat.finite_of_card_ne_zero (by rw [natCard_quot hK]; exact (pow_pos hp.out.pos 2).ne')
end PI.OkpW
