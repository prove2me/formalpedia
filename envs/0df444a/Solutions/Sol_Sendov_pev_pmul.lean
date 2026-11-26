-- Prove2me | solution 1 for Sendov.pev_pmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:09:53.57035+00:00
-- url     : https://prove2.me/submissions/cd2c6740-3845-4af3-9b75-92a8085dd041

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Theorems.Thm_Sendov_pev_nil
import Theorems.Thm_Sendov_pev_cons
import Theorems.Thm_Sendov_pev_padd
import Theorems.Thm_Sendov_pev_map_mul
attribute [local simp] Sendov.pev_nil
attribute [local simp] Sendov.pev_cons

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (p q : List ℤ) (x : ℝ) : pev (pmul p q) x = pev p x * pev q x := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    simp only [pmul, pev_padd, pev_map_mul, pev_cons, ih]
    push_cast
    ring
end Sendov
