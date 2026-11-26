-- Prove2me | solution 1 for Sendov.rev_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:57.271647+00:00
-- url     : https://prove2.me/submissions/829cb5f0-1101-426f-8855-dd3716969764

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
theorem _root_.solution (r : List (List ℤ)) (α t : ℝ) :
    rev (([] : List ℤ) :: r) α t = t * rev r α t := by
  simp
end Sendov
