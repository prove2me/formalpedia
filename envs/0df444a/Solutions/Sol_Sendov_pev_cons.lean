-- Prove2me | solution 1 for Sendov.pev_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:01.267213+00:00
-- url     : https://prove2.me/submissions/aca04379-dc6d-423b-8aec-f1e8464ee73b

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (a : ℤ) (p : List ℤ) (x : ℝ) :
    pev (a :: p) x = (a : ℝ) + x * pev p x := rfl
end Sendov
