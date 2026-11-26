-- Prove2me | solution 1 for Sendov.gg0_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:59.491652+00:00
-- url     : https://prove2.me/submissions/c506b65f-10fe-44bf-99cd-72438fe2b84a

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Recurrence

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution (n : ℕ) : (gg0 n).length = 2 := rfl
end Sendov
