-- Prove2me | solution 1 for Sendov.pev_padd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:37.381165+00:00
-- url     : https://prove2.me/submissions/32b4db29-a7bc-4b7f-985b-9c5c4974638c

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (p q : List ℤ) (x : ℝ) : pev (padd p q) x = pev p x + pev q x := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, pev_cons, ih]
      push_cast
      ring
end Sendov
