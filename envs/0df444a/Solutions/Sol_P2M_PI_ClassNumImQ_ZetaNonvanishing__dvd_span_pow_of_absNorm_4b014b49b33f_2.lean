-- Prove2me | solution 2 for P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:13:00.205585+00:00
-- url     : https://prove2.me/submissions/704a87ed-2cc0-4ada-942f-02b6c012c8bd

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
theorem _root_.solution {p k : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    I ∣ Ideal.span {(p : 𝓞 K)} ^ k := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  have hm := Ideal.absNorm_mem I
  rw [hI] at hm
  simpa using hm
end PI.ClassNumImQ.ZetaNonvanishing₂
