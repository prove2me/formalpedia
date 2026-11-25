-- Prove2me | solution 1 for PI.EF.kb_le_nearB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:44.501473+00:00
-- url     : https://prove2.me/submissions/be2f3d00-9332-4140-a98a-2cf7fbb63542

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSum
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronSumBound
import Theorems.Thm_PI_EF_kb_le_div
import Theorems.Thm_PI_EF_kb_le_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Finset
namespace PI.EF
theorem _root_.solution {u T : ℝ} (hu : 0 < u) (hT : 0 < T) {n : ℕ} (hn : 0 < n)
    (hn2 : (n : ℝ) < 2 * u) : kb T (u / n) ≤ nearB u T n := by
  have hx : (0 : ℝ) < n := by exact_mod_cast hn
  have f1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu.le
  have f2 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
  unfold nearB
  split_ifs with h1 h2
  · have h3 : (n : ℝ) < ⌊u⌋₊ := by exact_mod_cast h1
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (le_abs_self _)
    linarith
  · exact kb_le_two hT _
  · have h3 : ((⌊u⌋₊ : ℝ) + 1) < n := by exact_mod_cast not_le.mp h2
    apply kb_le_div hu hT hx hn2 (by linarith)
    refine le_trans ?_ (neg_le_abs _)
    linarith
end PI.EF
