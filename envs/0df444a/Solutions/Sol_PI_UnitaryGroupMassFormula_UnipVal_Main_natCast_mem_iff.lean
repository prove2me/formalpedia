-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnipVal.Main.natCast_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:47:58.808965+00:00
-- url     : https://prove2.me/submissions/85e61a3e-f558-4bd0-a01d-67e156049997

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
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (m : ℕ) :
    ((m : 𝓞 K) ∈ w.asIdeal) ↔ plc w ∣ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, plc, ringChar.spec]
end PI.UnitaryGroupMassFormula.UnipVal.Main
