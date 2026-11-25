-- Prove2me | solution 1 for PI.WFJM.Shape.getD_pad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:05:36.638942+00:00
-- url     : https://prove2.me/submissions/fe185391-5a42-4885-bcd8-eb54ca115eae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_GlobalTheory
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeFromFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.WFJM PI.WFJM.Shape
open PI.FJM
variable {n : ℕ}
namespace PI.WFJM.Shape
theorem _root_.solution (x y : List ℤ) (k i : ℕ) : (pad x k y).getD i 0 =
    if h : i < x.length then ((x[i] : ℤ) : ℚ) else if i < x.length + k then 0
      else ((y.getD (i - x.length - k) 0 : ℤ) : ℚ) := by
  unfold pad
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left h1]
    simp [h1]
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega)]
    simp [List.getElem?_replicate, show i - x.length < k by omega]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_replicate]
    rw [List.getD_eq_getElem?_getD]
    have : i - (x.length + k) = i - x.length - k := by omega
    rw [this]
    cases y[i - x.length - k]? <;> simp
end PI.WFJM.Shape
