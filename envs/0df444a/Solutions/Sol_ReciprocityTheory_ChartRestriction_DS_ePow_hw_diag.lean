-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.ePow_hw_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:58:39.370692+00:00
-- url     : https://prove2.me/submissions/48ea6f4d-d8c9-4ddf-b1d4-6fb6ff4132b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_Gelfand
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandHW
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ePow_hw_lower
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
    (hv : IsHWVec E ν v) (k : ℕ) (r : Fin n) : ePow E k r r v = gx (hwShift ν) k r • v := by
  induction k generalizing r with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, gx]
  | succ k ih =>
    have key : ∀ c, E r c (ePow E k c r v) =
        ((if c = r then (ν r : ℂ) * gx (hwShift ν) k r else 0) +
         (if r < c then gx (hwShift ν) k r - gx (hwShift ν) k c else 0)) • v := by
      intro c
      rcases lt_trichotomy c r with h | h | h
      · rw [ePow_hw_lower hE hv k c r h, map_zero, if_neg h.ne, if_neg (not_lt.2 h.le)]
        simp
      · subst h
        rw [ih, LinearMap.map_smul, hv.1, smul_smul, if_pos rfl, if_neg (lt_irrefl _), add_zero,
          mul_comm]
      · have hc := ePow_comm hE k r c c r
        rw [if_pos rfl, if_pos rfl] at hc
        have hc' := congrArg (fun f => f v) hc
        simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc'
        rw [hv.2 r c h, map_zero, sub_zero, ih, ih c] at hc'
        rw [if_neg h.ne', if_pos h, zero_add, sub_smul]
        exact hc'
    rw [show ePow E (k + 1) r r = ∑ c, E r c * ePow E k c r from by simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply], LinearMap.sum_apply]
    simp only [Module.End.mul_apply, key]
    rw [← Finset.sum_smul]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (Finset.mem_univ _), ← Finset.sum_filter,
      Finset.sum_sub_distrib, Finset.sum_const]
    have hf : (univ.filter fun c => r < c) = Finset.Ioi r := by ext; simp
    rw [hf, Fin.card_Ioi, nsmul_eq_mul]
    simp only [gx, hwShift, hf]
    push_cast
    ring
end ReciprocityTheory.ChartRestriction.DS
