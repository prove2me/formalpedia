-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__span_le_of_absNorm_fd6c4dee4894
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:10:20.814224+00:00
-- url     : https://prove2.me/submissions/879ef6d1-e86c-47d6-b986-27438f185255

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticDedekindZeta_SpanNatCastSupEqTop

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
theorem _root_.solution {I : Ideal (𝓞 K)} {m : ℕ} (hI : Ideal.absNorm I = m) :
    Ideal.span {(m : 𝓞 K)} ≤ I := by
  rw [← hI]
  exact Ideal.span_singleton_absNorm_le I
end PI.ClassNumImQ.ZetaNonvanishing₂
