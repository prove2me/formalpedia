-- Prove2me | solution 1 for P2M_RH_P2M_PI_ClassNumImQ_ZetaNonvanishing__cnt_one_f98a1623b55b_697d2cc9c3d8fc66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:56:06.257353+00:00
-- url     : https://prove2.me/submissions/496206b1-d75d-4c86-be51-1a235bfbb7d1

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
theorem _root_.solution : cnt K 1 = 1 := by
  unfold cnt
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨⊤, Ideal.absNorm_top⟩, fun y => Subtype.ext (Ideal.absNorm_eq_one_iff.mp y.2)⟩
end PI.ClassNumImQ.ZetaNonvanishing₂
