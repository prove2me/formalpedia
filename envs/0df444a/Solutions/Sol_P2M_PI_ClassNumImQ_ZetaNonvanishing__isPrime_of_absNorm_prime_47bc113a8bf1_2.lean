-- Prove2me | solution 2 for P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:13:14.350212+00:00
-- url     : https://prove2.me/submissions/8d3eff8a-4d51-4b80-96ab-fb7ee8e90601

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = p) : P.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm (by rw [hP]; exact (Nat.prime_iff.mp hp).irreducible)
end PI.ClassNumImQ.ZetaNonvanishing₂
