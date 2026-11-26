-- Prove2me | solution 1 for Sendov.integral_moment_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:13:16.099343+00:00
-- url     : https://prove2.me/submissions/9229c824-23e3-44c0-9aeb-d4f0fdeb6144

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_integral_moment_rec
import Theorems.Thm_Sendov_DQ_eq
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = irow (qrow (gg0 n) (gg1 n) (gg2 n) k) 0 α / (2 * M n * (3 + α)) ^ k := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  exact integral_moment_rec (n := n) (k := k) (by positivity) (fun t => DQ_eq n hn α t hα)
end Sendov
