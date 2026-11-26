-- Prove2me | solution 1 for Sendov.continuous_rev
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:57.783432+00:00
-- url     : https://prove2.me/submissions/4fa25cd7-a567-4d6f-af44-95214d897a13

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_rev_nil
import Theorems.Thm_Sendov_rev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons
attribute [local simp] Sendov.rev_nil
attribute [local simp] Sendov.rev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (r : List (List ℤ)) (α : ℝ) : Continuous fun t : ℝ => rev r α t := by
  induction r with
  | nil => simpa using continuous_const
  | cons p r ih =>
    simp only [rev_cons]
    exact continuous_const.add (continuous_id.mul ih)
end Sendov
