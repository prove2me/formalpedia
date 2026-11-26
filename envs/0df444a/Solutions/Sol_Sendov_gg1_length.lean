-- Prove2me | solution 1 for Sendov.gg1_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:05.848539+00:00
-- url     : https://prove2.me/submissions/55af9c69-5352-49d2-b15c-7d5f2069ae49

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (n : ℕ) : (gg1 n).length = 3 := rfl
end Sendov
