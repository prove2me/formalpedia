-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_output_chart_eq_of_mulVec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/8869b0b3-c6a4-45de-8960-827b21e6cea7

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k m : ℕ}
    (g : (Fin (k + 1) → ℂ) → (Fin (m + 1) → ℂ))
    (j : Fin (k + 1)) (ell : Fin (m + 1))
    (w : Fin (k + 1) → ℂ) (hwj : w j = 1)
    (hell : g w ell ≠ 0)
    (A : Matrix (Fin (k + 1)) (Fin (m + 1)) ℂ)
    (hA : Matrix.mulVec A (g w) = 0) :
    permanentRolloutOutputChart g j ell
        (j.removeNth w,
          fun r q => A r (ell.succAbove q)) = A := by
  have hnormalize :
      permanentRolloutNormalizedInput j (j.removeNth w) = w := by
    simpa only [permanentRolloutNormalizedInput, hwj] using
      Fin.insertNth_self_removeNth j w
  funext r
  funext q
  induction q using Fin.succAboveCases ell with
  | p q =>
      simp [permanentRolloutOutputChart]
  | x =>
      simp only [permanentRolloutOutputChart,
        Fin.insertNth_apply_same, hnormalize]
      have hrow : ∑ q : Fin (m + 1), A r q * g w q = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hA r
      rw [Fin.sum_univ_succAbove (fun q => A r q * g w q) ell] at hrow
      field_simp
      linear_combination -hrow
end PermanentRollout
