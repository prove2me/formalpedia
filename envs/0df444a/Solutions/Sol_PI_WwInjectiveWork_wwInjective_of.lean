-- Prove2me | solution 1 for PI.WwInjectiveWork.wwInjective_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:15.213898+00:00
-- url     : https://prove2.me/submissions/4811fb41-0549-48aa-ae6d-080c2d75da83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_GramVanish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
import Theorems.Thm_PI_WwInjectiveWork_sum_smul_eq_zero
import Theorems.Thm_PI_WwInjectiveWork_gram_vanish


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwInjectiveWork
open MvPolynomial PI.WwInjective PI.WwInjective.KM
variable {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
namespace PI.WwInjectiveWork
theorem _root_.solution (hCB : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by
  unfold PI.WwInjective.WwInjective
  intro Lt _ _ l _ N nu ph hph J
  exact gram_vanish (fun J => nablaX N nu J) ph (sum_smul_eq_zero N nu hCB l ph hph) J
end PI.WwInjectiveWork
