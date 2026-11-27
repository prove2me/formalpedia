-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:40.630505+00:00
-- url     : https://prove2.me/submissions/17d10e40-c301-47b6-a79c-d207717435b3

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution : Real.exp (1 / 3) < 2 := by
  calc Real.exp (1 / 3) < Real.exp (Real.log 2) :=
        Real.exp_lt_exp.mpr (by have := Real.log_two_gt_d9; linarith)
    _ = 2 := Real.exp_log (by norm_num)
end ReciprocityTheory.MultiplicativeHeights
