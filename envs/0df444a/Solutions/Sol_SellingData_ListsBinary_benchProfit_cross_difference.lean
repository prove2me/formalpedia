-- Prove2me | solution 1 for SellingData.ListsBinary.benchProfit_cross_difference
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:32:37.007999+00:00
-- url     : https://prove2.me/submissions/f2ce510e-e7fe-479f-9667-2dc6dcf74896

import Mathlib
import Definitions.Def_SellingData_ListsBinary_Setting
set_option autoImplicit false
open SellingData.ListsBinary

theorem solution (M : Model) (θi c c' α α' : ℝ) :
    (M.benchProfit θi c' α' - M.benchProfit θi c' α) -
        (M.benchProfit θi c α' - M.benchProfit θi c α) =
      θi * (1 - 2 * M.phi) * (α' - α) * (c' - c) := by
  unfold Model.benchProfit sigmaH
  ring
