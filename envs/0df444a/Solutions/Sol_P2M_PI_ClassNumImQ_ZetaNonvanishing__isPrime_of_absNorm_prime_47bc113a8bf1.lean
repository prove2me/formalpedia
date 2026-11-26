-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__isPrime_of_absNorm_prime_47bc113a8bf1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:02:36.318943+00:00
-- url     : https://prove2.me/submissions/8111ec00-9de3-4159-9c01-16be480c3305

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) {P : Ideal (𝓞 K)}
    (hP : Ideal.absNorm P = p) : P.IsPrime := by
  exact Ideal.isPrime_of_irreducible_absNorm (by rw [hP]; exact hp.prime.irreducible)



