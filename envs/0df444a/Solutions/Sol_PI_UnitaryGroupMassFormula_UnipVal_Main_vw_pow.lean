-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.vw_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:48:05.327356+00:00
-- url     : https://prove2.me/submissions/5dc21b8a-bae7-4e6c-96be-77dd5323aca2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnipVal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentValuation_VwIntEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnipVal PI.UnitaryGroupMassFormula.UnipVal.Main
open PI.UnipVal
variable {K : Type} [Field K] [NumberField K]
namespace PI.UnitaryGroupMassFormula.UnipVal.Main
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (x : K) (k : ℕ) : vw w (x ^ k) = k * vw w x := by
  simp only [vw]
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]
end PI.UnitaryGroupMassFormula.UnipVal.Main
