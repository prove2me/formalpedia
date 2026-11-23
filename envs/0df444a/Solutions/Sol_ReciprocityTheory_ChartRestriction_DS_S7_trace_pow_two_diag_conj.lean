-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.trace_pow_two_diag_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:10:48.083809+00:00
-- url     : https://prove2.me/submissions/93983ba8-dad2-4800-80a0-e4ffc7f24f5b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_UhU
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_entry


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
    (i : ℕ) :
    ∑ k, (y k : ℂ) ^ 2 * dmK U i k k = ∑ a, dmChi i a * ∑ b, Y a b * Y b a := by
  have hYY : Y * Y = U * Matrix.diagonal (fun j => (y j : ℂ) ^ 2) * Uᴴ := by
    rw [hY]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, dm_UhU hU, Matrix.one_mul, ← Matrix.mul_assoc (Matrix.diagonal _),
      Matrix.diagonal_mul_diagonal]
    simp only [sq]
  have hrow : ∀ a, ∑ b, Y a b * Y b a = ∑ k, U a k * (y k : ℂ) ^ 2 * star (U a k) := by
    intro a
    rw [← Matrix.mul_apply, hYY, dm_entry]
  simp only [hrow, dmK, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => ?_
  ring
end ReciprocityTheory.ChartRestriction.DS.S7
