-- Prove2me | solution 1 for Sendov.rev_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:58:07.410524+00:00
-- url     : https://prove2.me/submissions/2eba3ddb-8482-458f-b635-a9e222bfe6d0

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (p : List ℤ) (r : List (List ℤ)) (α t : ℝ) :
    rev (p :: r) α t = pev p α + t * rev r α t := rfl
end Sendov
