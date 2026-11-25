-- Prove2me | solution 1 for P2M_HalfIntGap__gap_673ecf939950
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:55:20.905117+00:00
-- url     : https://prove2.me/submissions/a1c30298-ad0b-4f63-a210-6c2944843825

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_UnitTraceSumBounds_CBCardNC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HalfIntegerGap_IntGap
import Theorems.Thm_P2M_HalfIntGap__int_gap_99de07923174

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HalfIntGap₂
namespace HalfIntGap₂
theorem _root_.solution (N : ℕ) (lam : Fin N → ℝ) (c : ℝ) (hlam : StrictAnti lam)
    (hc : ∀ a, ∃ m : ℤ, lam a - c = m) (a b : Fin N) (hab : a < b) :
    ((b.val : ℝ) - a.val) ≤ lam a - lam b := by
  choose m hm using hc
  have hanti : StrictAnti m := by
    intro x y hxy
    have h := hlam hxy
    have hx : lam x = c + m x := by linarith [hm x]
    have hy : lam y = c + m y := by linarith [hm y]
    rw [hx, hy] at h
    exact_mod_cast (by linarith : (m y : ℝ) < m x)
  have hle : a.val ≤ b.val := le_of_lt (Fin.lt_def.mp hab)
  have key := int_gap m hanti (b.val - a.val) a b (by omega)
  have key' : ((b.val : ℤ) - a.val) ≤ m a - m b := by
    have : ((b.val - a.val : ℕ) : ℤ) = (b.val : ℤ) - a.val := by omega
    omega
  have hreal : ((b.val : ℝ) - a.val) ≤ (m a : ℝ) - m b := by exact_mod_cast key'
  have ha : lam a = c + m a := by linarith [hm a]
  have hb : lam b = c + m b := by linarith [hm b]
  rw [ha, hb]
  linarith
end HalfIntGap₂
