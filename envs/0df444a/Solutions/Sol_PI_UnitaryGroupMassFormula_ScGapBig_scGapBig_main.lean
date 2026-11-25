-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ScGapBig.scGapBig_main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:50:53.237549+00:00
-- url     : https://prove2.me/submissions/a1259f27-ba0f-439b-a86e-f16271b2fce5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SpectralGapLarge_ScGapBigMain
import Theorems.Thm_PI_UnitaryGroupMassFormula_ScGapBig_nat_bound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ScGapBig
open PI.ScGapBig
namespace PI.UnitaryGroupMassFormula.ScGapBig
theorem _root_.solution : ScGapBig := by
  intro k r b hn hgap
  have hrk : rk48 k r = 2 * r + k + 1 := rfl
  obtain ⟨t, hodd, ht1, ht2⟩ : ∃ t : ℕ, Odd t ∧ rk48 k r + 5 ≤ t ∧ t ≤ rk48 k r + 6 := by
    rcases Nat.even_or_odd (rk48 k r) with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨rk48 k r + 5, ⟨a + 2, by omega⟩, le_refl _, by omega⟩
    · exact ⟨rk48 k r + 6, ⟨a + 3, by omega⟩, by omega, le_refl _⟩
  refine ⟨t, hodd, ht1, by omega, ?_⟩
  intro j hj
  have hm : 2 * r + 2 ≤ rk48 k r + 1 := by omega
  have hb := nat_bound (rk48 k r) (2 * r + 2) t hn hm ht2
  have hcast : 2 * ((rk48 k r + (2 * r + 2) * t : ℕ) : ℝ) ^ 3 + (t : ℝ) + 3 <
      16 * (rk48 k r : ℝ) ^ 19 := by
    exact_mod_cast hb
  linarith [hgap j hj]
end PI.UnitaryGroupMassFormula.ScGapBig
