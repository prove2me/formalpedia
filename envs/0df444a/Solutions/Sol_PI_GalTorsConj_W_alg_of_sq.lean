-- Prove2me | solution 1 for PI.GalTorsConj.W.alg_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:41:02.608159+00:00
-- url     : https://prove2.me/submissions/a0e7bdc4-34a5-4d61-9552-c0f07b3a2fca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_IncAdjInclusion
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpOnto
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_AddDbl
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_TorsValsFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.GalTorsConj PI.GalTorsConj.W
open Polynomial Formalism.L2.Th1.F
namespace PI.GalTorsConj.W
theorem _root_.solution {F : Type*} [Field F] [Algebra F ℂ] {x y a b : ℂ}
    (hsq : y ^ 2 = 4 * x ^ 3 - a * x - b)
    (hx : IsAlgebraic F x) (ha : IsAlgebraic F a) (hb : IsAlgebraic F b) : IsAlgebraic F y := by
  have hx' := mem_algebraicClosure_iff.mpr hx
  have ha' := mem_algebraicClosure_iff.mpr ha
  have hb' := mem_algebraicClosure_iff.mpr hb
  have h4 : (4 : ℂ) ∈ algebraicClosure F ℂ := by
    have := natCast_mem (algebraicClosure F ℂ) 4
    exact_mod_cast this
  have hw : 4 * x ^ 3 - a * x - b ∈ algebraicClosure F ℂ :=
    sub_mem (sub_mem (mul_mem h4 (pow_mem hx' 3)) (mul_mem ha' hx')) hb'
  rw [← hsq] at hw
  exact IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.mp hw)
end PI.GalTorsConj.W
