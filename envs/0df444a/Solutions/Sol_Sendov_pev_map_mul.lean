-- Prove2me | solution 1 for Sendov.pev_map_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:36.962615+00:00
-- url     : https://prove2.me/submissions/498077df-9884-4db0-9b3d-790b51957abc

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
theorem _root_.solution (a : ℤ) (q : List ℤ) (x : ℝ) :
    pev (q.map (fun b => a * b)) x = (a : ℝ) * pev q x := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, pev_cons, ih]
    push_cast
    ring
end Sendov
