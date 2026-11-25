-- Prove2me | solution 1 for PI.RayBoundIQW.gen_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:13:05.614074+00:00
-- url     : https://prove2.me/submissions/f0b178ec-c2c6-4c4b-9118-b044ed2e6084

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
theorem _root_.solution (J : PrimeTo qq) : gen qq J ≠ 0 := by
  intro h
  have e := gen_spec qq J
  rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at e
  have hJ : J.1 ≠ 0 := J.2.1
  have hB : (base qq (cls qq J)).1 ^ (classNumber K0 - 1) ≠ 0 :=
    pow_ne_zero _ (base qq (cls qq J)).2.1
  exact mul_ne_zero hJ hB (by rw [← e]; rfl)
end PI.RayBoundIQW
