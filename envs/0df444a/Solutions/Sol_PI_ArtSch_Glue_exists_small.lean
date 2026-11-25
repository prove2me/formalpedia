-- Prove2me | solution 1 for PI.ArtSch.Glue.exists_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:08.011879+00:00
-- url     : https://prove2.me/submissions/4ebac773-b2a0-4f8c-babe-28f167c3c26f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationGluing_ValbLeOfCoeffEqZero
import Theorems.Thm_PI_ArtSch_Glue_v_l_lt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ArtSch PI.ArtSch.Glue
open scoped NNReal
noncomputable section
variable {l : ℕ} [hl : Fact l.Prime]
namespace PI.ArtSch.Glue
theorem _root_.solution (t : ℝ≥0) (ht : 0 < t) :
    ∃ n : ℕ, (PadicComplex.valued l).v ((l : ℕ) : PadicComplex l) ^ (l ^ n) < t := by
  have hq := v_l_lt_one (l := l)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ht hq
  exact ⟨n, lt_of_le_of_lt (pow_le_pow_of_le_one zero_le hq.le
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le) hn⟩
end PI.ArtSch.Glue
