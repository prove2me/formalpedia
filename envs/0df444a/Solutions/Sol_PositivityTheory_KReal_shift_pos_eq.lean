-- Prove2me | solution 1 for PositivityTheory.KReal.shift_pos_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:44:43.075194+00:00
-- url     : https://prove2.me/submissions/f86c2531-8e3a-4cf9-abfe-bd84eb7bb18b

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Theorems.Thm_PositivityTheory_KReal_getD_pad_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution (p q r s n m : ℕ) :
    shiftNu (cPair p q) (laPos p q r s n m) =
      ofBlocks (pad (List.replicate p (n : ℤ)) (r - p) []) (pad (List.replicate q (m : ℤ)) (s - q) []) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laPos, ofBlocks, getD_pad_left]
    split_ifs <;> push_cast <;> ring
end PositivityTheory.KReal
