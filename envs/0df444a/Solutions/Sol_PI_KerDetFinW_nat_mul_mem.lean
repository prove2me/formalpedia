-- Prove2me | solution 1 for PI.KerDetFinW.nat_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:23.325876+00:00
-- url     : https://prove2.me/submissions/71e53015-8b62-46fb-bbdb-cf484af7f7df

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsNatMulMemFracFam

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
open PI PI.KerDetFinW
open PI.KerIso
namespace PI.KerDetFinW
theorem _root_.solution {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (c : ℕ) {y : E} (hy : y ∈ I) :
    (c : E) * y ∈ I := by
  have := (I : Submodule (𝓞 E) E).smul_mem (c : 𝓞 E) hy
  rw [Algebra.smul_def, map_natCast] at this
  exact this
end PI.KerDetFinW
