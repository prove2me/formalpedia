-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:14:58.836865+00:00
-- url     : https://prove2.me/submissions/f11ad907-1128-44f2-9c5a-fb92cffdd412

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_trace_diag_conj_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_S
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_minorWeights_indicator


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {U Y : Matrix (Fin n) (Fin n) ℂ} {y : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ)
    (hd : ∀ a, Y a a = 0) {i : ℕ} (hi : i ≤ n) :
    ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * ((∑ j ∈ J.1, y j : ℝ) : ℂ) = 0 := by
  simp only [dm_S, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ k, ∑ J : {J : Finset (Fin n) // J.card = i}, ((dmW U hi J : ℝ) : ℂ) * (dmInd J.1 k * (y k : ℂ)) =
      (y k : ℂ) * dmK U i k k := by
    intro k
    rw [← sum_minorWeights_indicator hU hi k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J _ => ?_
    ring
  simp only [h, trace_diag_conj_eq hY, hd, mul_zero, Finset.sum_const_zero]
end ReciprocityTheory.ChartRestriction.DS.S7
