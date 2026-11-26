-- Prove2me | solution 1 for Sendov.rev_radd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:56.712436+00:00
-- url     : https://prove2.me/submissions/0c4f57cc-968f-49e6-a6c5-591a80c24634

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_padd
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
theorem _root_.solution (r s : List (List ℤ)) (α t : ℝ) :
    rev (radd r s) α t = rev r α t + rev s α t := by
  induction r generalizing s with
  | nil => simp [radd]
  | cons p r ih =>
    cases s with
    | nil => simp [radd]
    | cons q s =>
      simp only [radd, rev_cons, pev_padd, ih]
      ring
end Sendov
