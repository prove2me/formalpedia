-- Prove2me | solution 1 for PI.FJMX.pad_getD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:45:33.091043+00:00
-- url     : https://prove2.me/submissions/c4f789c0-2f1f-4d33-aa1f-0ce16d847e60

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistPad
import Theorems.Thm_PI_FJMX_posPart_getD
import Theorems.Thm_PI_FJMX_negPart_getD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FockH1Action PI.FJM
noncomputable section
open PI PI.FJMX
namespace PI.FJMX
theorem _root_.solution (a b : List ℤ) (n : ℕ) (hn : a.length + b.length ≤ n) (ha : ∀ v ∈ a, 0 < v)
    (hb : ∀ v ∈ b, v < 0) (i : ℕ) (hi : i < n) :
    (pad a (n - a.length - b.length) b).getD i 0 =
      ((PI.FJM.posPart a).getD i 0 : ℚ) - ((PI.FJM.negPart b).getD (n - 1 - i) 0 : ℚ) := by
  rw [posPart_getD a ha, negPart_getD b hb]
  rw [pad, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map]
  by_cases h1 : i < a.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1,
      dif_pos h1, dif_neg (by omega)]
    simp
  · by_cases h2 : i < a.length + (n - a.length - b.length)
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
        dif_neg h1, dif_neg (by omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega), dif_neg h1, dif_pos (by omega)]
      simp only [neg_neg, sub_neg_eq_add, zero_add]
      congr 2
      simp
      omega
end PI.FJMX
