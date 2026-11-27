-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.dm_hs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:27:04.346092+00:00
-- url     : https://prove2.me/submissions/e6436189-9819-43b9-9622-b9c79af80a2c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_herm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_trace_pow_two_diag_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_UhU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_normsq


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
theorem _root_.solution (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : Y = U * Matrix.diagonal (fun j => (y j : ℂ)) * Uᴴ) :
    hs Y = ∑ k, y k ^ 2 := by
  apply Complex.ofReal_injective
  have h3 := trace_pow_two_diag_conj hU hY n
  have hchi : ∀ a : Fin n, dmChi n a = 1 := by intro a; simp [dmChi, a.isLt]
  have hKn : ∀ k, dmK U n k k = 1 := by
    intro k
    have h := congrFun (congrFun (dm_UhU hU) k) k
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp only [dmK, hchi, one_mul]
    rw [← h]
    rfl
  simp only [hchi, hKn, one_mul, mul_one] at h3
  rw [hs, Complex.ofReal_sum, Complex.ofReal_sum]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, h3]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.ofReal_pow, dm_normsq, ← dm_herm hY a b]
end ReciprocityTheory.ChartRestriction.DS.S7
