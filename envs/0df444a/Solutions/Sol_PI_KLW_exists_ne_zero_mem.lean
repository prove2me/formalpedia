-- Prove2me | solution 1 for PI.KLW.exists_ne_zero_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:06:54.296354+00:00
-- url     : https://prove2.me/submissions/619fdf3a-6927-49c0-9dbe-ef70b9715fd3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_EquivariantPartsOfFiniteType
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeIsomorphism_PairingFactorsThroughPeriods
import Theorems.Thm_PI_KLW_Unimod_zero_mem


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
theorem _root_.solution (cj : E ≃ₐ[ℚ] E) (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hI : PI.KerIso.SelfDualI K cj I) : ∃ y0 ∈ I, y0 ≠ 0 := by
  by_contra hne
  push Not at hne
  have h1 : (1 : E) ∈ I := (hI 1).2 fun z hz => by
    rw [hne z hz, zero_mul, map_zero]; exact zero_mem _
  exact one_ne_zero (hne 1 h1)
end PI.KLW
