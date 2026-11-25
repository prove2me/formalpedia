-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ePow_hw_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:42:25.546955+00:00
-- url     : https://prove2.me/submissions/c72b8b8d-521d-4166-971b-503d2d32d88e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_comm


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
variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {E : Fin n → Fin n → Module.End ℂ M} (hE : IsGlRep E) {ν : Fin n → ℝ} {v : M}
    (hv : IsHWVec E ν v) (k : ℕ) (s r : Fin n) (hsr : s < r) : ePow E k s r v = 0 := by
  induction k generalizing s r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, hsr.ne]
  | succ k ih =>
    rw [show ePow E (k + 1) s r = ∑ c, E s c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro c _
    rw [Module.End.mul_apply]
    rcases lt_or_ge c r with hcr | hrc
    · rw [ih c r hcr, map_zero]
    · have hc := ePow_comm hE k s c c r
      rw [if_pos rfl, if_neg hsr.ne'] at hc
      have hc' := congrArg (fun f => f v) hc
      simp only [LinearMap.sub_apply, Module.End.mul_apply, sub_zero] at hc'
      rw [hv.2 s c (lt_of_lt_of_le hsr hrc), map_zero, sub_zero, ih s r hsr] at hc'
      exact hc'
end ReciprocityTheory.ChartRestriction.DS
