-- Prove2me | solution 1 for QEC.Coding.ReedMuller.reedMullerCode_dimension_eq_card_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:21:59.578214+00:00
-- url     : https://prove2.me/submissions/13b0c8ae-09d8-4972-b2cb-9b2532004239

import Definitions.Def_QEC_Coding_Core_Definitions
import Definitions.Def_QEC_Coding_ReedMuller_Base
import Theorems.Thm_QEC_Coding_ReedMuller_evaluationLinearMap_injective

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Coding
open QEC.Coding.ReedMuller
open scoped BigOperators
namespace QEC.Coding.ReedMuller
theorem _root_.solution (r m : Nat) :
    Dimension (reedMullerCode r m) = Fintype.card (SquarefreeMonomial m r) := by
  change Module.finrank (ZMod 2) (LinearMap.range (evaluationLinearMap m r)) = _
  rw [LinearMap.finrank_range_of_inj (evaluationLinearMap_injective m r)]
  exact
    (Module.finrank_fintype_fun_eq_card (ZMod 2)
      (η := SquarefreeMonomial m r))
end QEC.Coding.ReedMuller
