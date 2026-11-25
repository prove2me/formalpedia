-- Prove2me | solution 1 for PI.KLW.natCast_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:44:53.568577+00:00
-- url     : https://prove2.me/submissions/36a9e2e1-c9d2-44a6-915b-7b64018b0487

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Theorems.Thm_PI_KLW_Unimod_smul_mem


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
variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]
namespace PI.KLW
theorem _root_.solution (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (q : ℕ) {z : E}
    (hz : z ∈ I) : (q : E) * z ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (q : 𝓞 E) hz
  rwa [Algebra.smul_def, map_natCast] at this
end PI.KLW
