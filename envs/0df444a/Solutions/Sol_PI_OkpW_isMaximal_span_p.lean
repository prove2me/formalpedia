-- Prove2me | solution 1 for PI.OkpW.isMaximal_span_p
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:15.645279+00:00
-- url     : https://prove2.me/submissions/3c6ea548-3bc5-49e1-94aa-55677f67bf94

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_OkpInert
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertPrimeTeichmuller_NormLeOneOfIntegralInt
import Theorems.Thm_PI_OkpW_span_p_ne_bot

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
theorem _root_.solution (hP : (Ideal.span {(p : 𝓞 K)}).IsPrime) :
    (Ideal.span {(p : 𝓞 K)}).IsMaximal :=
  hP.isMaximal span_p_ne_bot
end PI.OkpW
