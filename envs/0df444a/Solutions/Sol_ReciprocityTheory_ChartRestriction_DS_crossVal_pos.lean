-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.crossVal_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:38:42.868167+00:00
-- url     : https://prove2.me/submissions/53d71e8a-d433-4aec-839c-4a5ec5cb0cc1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_casValK_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dot_rhoN_root_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_lowK_add_rhoC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_nsq_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
section Num
variable {ε : Fin n → Bool}
private theorem dot_add_l (u v w : Fin n → ℝ) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, sum_add_distrib]
private theorem dot_root_r (u : Fin n → ℝ) (a b : Fin n) : dot u (root a b) = u a - u b := by
  simp [dot, root, Pi.single_apply, mul_sub, sum_sub_distrib]
end Num
end ReciprocityTheory.ChartRestriction.DS
end
end

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {lam : Fin n → ℝ} (hmono : StrictAnti lam) {h : ℝ}
    (hh : GapAtLeast ε lam h) {a b : Fin n} (hab : a < b) (hε : ε a ≠ ε b) :
    2 * (h - n + 1) ≤
      casValK ε (lowK ε lam + root a b) - n - casValK ε (lowK ε lam) := by
  rw [casValK_add, lowK_add_rhoC, nsq_root (ne_of_lt hab), dot_add_l, dot_root_r lam]
  have h1 := hh a b hε
  rw [abs_of_pos (sub_pos.2 (hmono hab))] at h1
  have h2 := dot_rhoN_root_ge hab hε
  linarith
end ReciprocityTheory.ChartRestriction.DS
