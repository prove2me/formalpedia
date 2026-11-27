-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ratioVd_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:25:22.23091+00:00
-- url     : https://prove2.me/submissions/9103d986-4a94-4dd9-b242-50c5d8a14c0e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Resolvent
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Residue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_not_injective_shift_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {μ : Fin n → ℝ} (hμ : Function.Injective μ) (hint : ∀ a b, ∃ m : ℤ, μ a - μ b = (m : ℝ))
    (s : Fin n) : 0 ≤ ratioVd μ s ∧ (ratioVd μ s = 0 ↔ ¬ Function.Injective (μ - Pi.single s 1)) := by
  have hfac : ∀ s' ∈ univ.erase s, 0 ≤ (μ s - 1 - μ s') / (μ s - μ s') := by
    intro s' hs'
    obtain ⟨m, hm⟩ := hint s s'
    rw [show μ s - 1 - μ s' = (μ s - μ s') - 1 by ring, hm]
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero, sub_eq_zero] at hm
      exact (Finset.mem_erase.mp hs').1 (hμ hm).symm
    rcases lt_or_gt_of_ne hm0 with h | h
    · have h' : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
      exact div_nonneg_of_nonpos (by linarith) (by linarith)
    · have h' : (1 : ℝ) ≤ m := by exact_mod_cast h
      exact div_nonneg (by linarith) (by linarith)
  refine ⟨Finset.prod_nonneg hfac, ?_⟩
  rw [ratioVd, Finset.prod_eq_zero_iff,
    not_injective_shift_iff hμ s (-1) (by simp [sub_eq_add_neg])
      (fun x hx => by simp [Pi.single_apply, hx])]
  refine exists_congr fun s' => and_congr_right fun hs' => ?_
  have hd : μ s - μ s' ≠ 0 := sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hs').1 (hμ h).symm)
  rw [div_eq_zero_iff, or_iff_left hd]
  constructor <;> intro h <;> linarith
end ReciprocityTheory.ChartRestriction.DS
