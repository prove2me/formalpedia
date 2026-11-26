-- Prove2me | solution 1 for Sendov.Nmom20_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:18:46.917497+00:00
-- url     : https://prove2.me/submissions/04286bed-60dc-4d93-9b8f-3e8b1faaa29f

import Definitions.Def_Sendov_FiniteRange_PackBridge
import Definitions.Def_Sendov_FiniteRange_Reduce
import Definitions.Def_Sendov_FiniteRange_Degree20Packed
import Theorems.Thm_Sendov_wsum_eq_of_packed


set_option autoImplicit false
set_option linter.style.longLine false
set_option maxRecDepth 100000
open Sendov
namespace Sendov
theorem _root_.solution :
    Nmom20 = wsum L20 0 (qrow (gg0 20) (gg1 20) (gg2 20) 8) := by
  refine wsum_eq_of_packed (gg0 20) (gg1 20) (gg2 20) 8 L20 beta20 tau20 Nmom20
    (by norm_num [beta20]) (by norm_num [tau20]) ?_ ?_ ?_ ?_ ?_
  · decide
  · decide
  · decide
  · rfl
  · rfl
end Sendov
