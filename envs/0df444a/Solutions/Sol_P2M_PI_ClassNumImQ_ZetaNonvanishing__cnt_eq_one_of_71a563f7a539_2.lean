-- Prove2me | solution 2 for P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_eq_one_of_71a563f7a539
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:49.860275+00:00
-- url     : https://prove2.me/submissions/4c675e0c-5125-4e89-8dff-007a5ff6c350

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
theorem _root_.solution {n : ℕ} (X : Ideal (𝓞 K)) (hX : Ideal.absNorm X = n)
    (h : ∀ I : Ideal (𝓞 K), Ideal.absNorm I = n → I = X) : cnt K n = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun a b => Subtype.ext ((h a.1 a.2).trans (h b.1 b.2).symm)⟩, ⟨⟨X, hX⟩⟩⟩
end PI.ClassNumImQ.ZetaNonvanishing₂
