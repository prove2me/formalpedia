-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.sch_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:10.239264+00:00
-- url     : https://prove2.me/submissions/f9fcea35-6419-483b-b1a8-c53c904ace45

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_two_dot_rhoC_rhoN_le

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
theorem _root_.solution {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by
  obtain ⟨hanti, h, hg, hbig⟩ := hgap
  have h1 := hg a b hε
  have hlt : lam b < lam a := hanti hab
  rw [abs_of_pos (sub_pos.2 hlt)] at h1
  rw [dot_root_r]
  linarith [two_dot_rhoC_rhoN_le ε]
end ReciprocityTheory.ChartRestriction.DS
