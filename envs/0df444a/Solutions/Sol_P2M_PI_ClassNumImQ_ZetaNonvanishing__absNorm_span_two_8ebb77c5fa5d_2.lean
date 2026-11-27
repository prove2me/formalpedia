-- Prove2me | solution 2 for P2M_PI_ClassNumImQ_ZetaNonvanishing__absNorm_span_two_8ebb77c5fa5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:43.699598+00:00
-- url     : https://prove2.me/submissions/1991fca3-fbf9-4059-b66a-ec0d4b553053

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_GenBase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open PI PI.ClassNumImQ PI.ClassNumImQ.ZetaNonvanishing₂
variable {K : Type} [Field K] [NumberField K]
namespace PI.ClassNumImQ.ZetaNonvanishing₂
theorem _root_.solution (h2 : Module.finrank ℚ K = 2) (p : ℕ) :
    Ideal.absNorm (Ideal.span {(p : 𝓞 K)}) = p ^ 2 := by
  rw [Ideal.absNorm_span_singleton]
  have hn : Algebra.norm ℤ ((p : 𝓞 K)) = (p : ℤ) ^ 2 := by
    rw [show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, h2]
  rw [hn, Int.natAbs_pow, Int.natAbs_natCast]
end PI.ClassNumImQ.ZetaNonvanishing₂
