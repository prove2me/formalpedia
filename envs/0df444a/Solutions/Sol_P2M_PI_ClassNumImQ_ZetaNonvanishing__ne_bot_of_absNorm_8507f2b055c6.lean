-- Prove2me | solution 1 for P2M_PI_ClassNumImQ_ZetaNonvanishing__ne_bot_of_absNorm_8507f2b055c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:18:30.713846+00:00
-- url     : https://prove2.me/submissions/4132838c-2aaf-42d2-accf-15ec300fa826

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
theorem _root_.solution {P : Ideal (𝓞 K)} {n : ℕ} (hP : Ideal.absNorm P = n) (hn : n ≠ 0) :
    P ≠ ⊥ := by
  rintro rfl
  rw [Ideal.absNorm_bot] at hP
  exact hn hP.symm
end PI.ClassNumImQ.ZetaNonvanishing₂
