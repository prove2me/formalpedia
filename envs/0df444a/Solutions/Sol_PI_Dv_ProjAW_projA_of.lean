-- Prove2me | solution 1 for PI.Dv.ProjAW.projA_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:10:01.087626+00:00
-- url     : https://prove2.me/submissions/5ecc8893-9c27-4de4-96da-a86e63781520

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_MemDualLat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LengthIndex_IdxEqLen
import Theorems.Thm_PI_Dv_ProjAW_idx_le
import Theorems.Thm_PI_Dv_ProjAW_idx_eq_len
import Theorems.Thm_PI_Dv_ProjAW_dual_part
import Theorems.Thm_PI_Dv_ProjAW_lenAt_congr
import Theorems.Thm_PI_Dv_ProjAW_one_sub_idem
import Theorems.Thm_PI_Dv_ProjAW_one_sub_int
import Theorems.Thm_PI_Dv_ProjAW_part1
import Theorems.Thm_PI_Dv_ProjAW_part2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.Dv PI.Dv.ProjAW
open NumberField IsDedekindDomain Formalism.BasicNotions
namespace PI.Dv.ProjAW
theorem _root_.solution (hI : IdxCalc) : ProjA := by
  intro K _ _ _ _ A e n hP
  obtain ⟨hG, hn0, he, hn, -⟩ := hP
  have he1 := one_sub_idem A he
  have hn1 := one_sub_int A hn
  refine ⟨part1 A hn, part2 A he, ⟨quotEquiv A e⟩, fun w => ?_,
    fun ψ hψ => dual_part A hG he hn0 hn ψ hψ⟩
  have heq : idxAt w (imgE A e A.L) (cutE A e A.L) =
      idxAt w (imgE A (1 - e) A.L) (cutE A (1 - e) A.L) := by
    rw [idx_eq_len A w he, idx_eq_len A w he1, lenAt_congr w _ _ _ _ (quotEquiv A e)]
  refine ⟨heq, by rw [idx_eq_len A w he]; positivity, ?_⟩
  rcases le_total (dimE A e) (dimE A (1 - e)) with h | h
  · rw [min_eq_left h]
    exact idx_le A hI hG he hn0 hn w
  · rw [min_eq_right h, heq]
    exact idx_le A hI hG he1 hn0 hn1 w
end PI.Dv.ProjAW
