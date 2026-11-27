-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_ballRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:32:08.134165+00:00
-- url     : https://prove2.me/submissions/b49ffbcf-25cb-46a9-b55a-4d9fd0617bc5

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
theorem _root_.solution {r : ℕ} (hr : 0 < r) : 0 ≤ ballRatio r := by
  have h1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h7 : 1 / (7 * (r : ℝ)) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hx : 0 < 1 / (7 * (r : ℝ)) := by positivity
  unfold ballRatio
  apply div_nonneg <;> linarith
end ReciprocityTheory.MultiplicativeHeights
