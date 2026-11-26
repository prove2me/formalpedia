-- Prove2me | solution 1 for Sendov.rev_rscale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:10:59.269379+00:00
-- url     : https://prove2.me/submissions/403e9261-3e95-4ebc-b412-6fd25022be60

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_pmul
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
theorem _root_.solution (g : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (rscale g r) α t = pev g α * rev r α t := by
  induction r with
  | nil => simp [rscale]
  | cons p r ih =>
    simp only [rscale, List.map_cons, rev_cons, pev_pmul] at *
    rw [ih]
    ring
end Sendov
