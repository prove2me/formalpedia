-- Prove2me | solution 1 for Sendov.DQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:10:00.658799+00:00
-- url     : https://prove2.me/submissions/d0c824f5-4363-4923-9e19-33542f095cb6

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rev_cons
import Theorems.Thm_Sendov_gg0_length
import Theorems.Thm_Sendov_gg1_length
import Theorems.Thm_Sendov_gg2_length
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos

attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rev_cons
attribute [local simp] Sendov.gg0_length
attribute [local simp] Sendov.gg1_length
attribute [local simp] Sendov.gg2_length

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (n : ℕ) (hn : 2 ≤ n) (α t : ℝ) (hα : 0 ≤ α) :
    (2 * M n * (3 + α)) * Q n α t
      = pev (gg0 n) α + pev (gg1 n) α * t + pev (gg2 n) α * t ^ 2 := by
  have hM : ((n : ℝ) - 1) ≠ 0 := by
    have h := M_pos hn
    simp only [M] at h
    linarith
  have h3 : (3 : ℝ) + α ≠ 0 := (three_add_pos hα).ne'
  simp only [gg0, gg1, gg2, pev_cons, pev_nil, Q, c, A, M]
  push_cast
  field_simp
  ring
end Sendov
