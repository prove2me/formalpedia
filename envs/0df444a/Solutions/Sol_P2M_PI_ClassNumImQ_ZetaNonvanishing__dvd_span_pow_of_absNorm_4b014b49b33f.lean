-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__dvd_span_pow_of_absNorm_4b014b49b33f
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:02:37.046384+00:00
-- url     : https://prove2.me/submissions/83ed0bf5-2e6f-4055-ac09-9fdfa58e8b2c

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
theorem _root_.solution {p k : ℕ} {I : Ideal (𝓞 K)} (hI : Ideal.absNorm I = p ^ k) :
    I ∣ Ideal.span {(p : 𝓞 K)} ^ k := by
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
  have h := Ideal.absNorm_mem I
  rw [hI] at h
  simpa using h



