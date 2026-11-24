-- Prove2me | solution 1 for PI.KLW.Rp_natCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:33.758799+00:00
-- url     : https://prove2.me/submissions/d859275b-0ef7-4d80-9d25-33dfb243060e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_of_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open NumberField
open PI PI.KLW
variable {K : Type} [Field K] [NumberField K]
namespace PI.KLW
theorem _root_.solution {p : ℕ} (m : ℕ) : Rp K p (m : K) := Rp_of_isIntegral (by
  simpa using (isIntegral_algebraMap (R := ℤ) (A := K) (x := (m : ℤ))))
end PI.KLW
