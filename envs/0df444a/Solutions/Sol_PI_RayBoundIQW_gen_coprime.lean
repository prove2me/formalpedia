-- Prove2me | solution 1 for PI.RayBoundIQW.gen_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:01.240007+00:00
-- url     : https://prove2.me/submissions/08a66eb4-253f-4952-813f-c5a7aae900d5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ImaginaryQuadraticClassBound_GenCoprime
import Theorems.Thm_PI_RayBoundIQW_gen_spec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
open PI PI.RayBoundIQW
variable {K0 : Type} [Field K0] [NumberField K0] (qq : Ideal (𝓞 K0))
namespace PI.RayBoundIQW
theorem _root_.solution (J : PrimeTo qq) : Ideal.span {gen qq J} ⊔ qq = ⊤ := by
  rw [gen_spec, ← Ideal.isCoprime_iff_sup_eq]
  exact IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr J.2.2)
    (IsCoprime.pow_left (Ideal.isCoprime_iff_sup_eq.mpr (base qq (cls qq J)).2.2))
end PI.RayBoundIQW
