-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_card_window_fin_23e7026002b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:28.247174+00:00
-- url     : https://prove2.me/submissions/79cd8c35-41bb-40af-978c-9ebe0adfd82c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PRhoBound
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open Finset
namespace GroundTheory.Heights₂.Heights.FourB
theorem _root_.solution (n a b : ℕ) (hb : b ≤ n) :
    ∑ i : Fin n, (if a ≤ i.val ∧ i.val < b then (1 : ℝ) else 0) = ((b - a : ℕ) : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if a ≤ i ∧ i < b then (1 : ℝ) else 0) n,
    Finset.sum_boole]
  congr 2
  have : (Finset.range n).filter (fun i => a ≤ i ∧ i < b) = Finset.Ico a b := by
    ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [this, Nat.card_Ico]
end GroundTheory.Heights₂.Heights.FourB
