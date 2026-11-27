-- Prove2me | solution 2 for P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_zero_of_8b919f503d1d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:03.959625+00:00
-- url     : https://prove2.me/submissions/708e07e3-fe4f-4cc2-9eb8-5490ec298588

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
theorem _root_.solution {n : ℕ} (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I ≠ n) : cnt K n = 0 := by
  unfold cnt
  haveI : IsEmpty { I : Ideal (𝓞 K) // Ideal.absNorm I = n } := ⟨fun x => h x.1 x.2⟩
  exact Nat.card_of_isEmpty
end PI.ClassNumImQ.ZetaNonvanishing₂
