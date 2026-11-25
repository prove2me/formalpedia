-- Prove2me | solution 1 for PI.KLW.Rp_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:47:21.633678+00:00
-- url     : https://prove2.me/submissions/dbf52dd0-4bea-44ff-937d-d960600fb469

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_LatticeFromNormOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_RpOfIsIntegral
import Theorems.Thm_PI_KLW_Rp_intCast
import Theorems.Thm_PI_KLW_Rp_mul

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
theorem _root_.solution {p : ℕ} {x : K} (hx : Rp K p x) : Rp K p (-x) := by
  have := Rp_mul (Rp_intCast (K := K) (p := p) (-1)) hx
  simpa using this
end PI.KLW
