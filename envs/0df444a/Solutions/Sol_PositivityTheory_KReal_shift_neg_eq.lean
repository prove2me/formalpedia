-- Prove2me | solution 1 for PositivityTheory.KReal.shift_neg_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:32:53.322196+00:00
-- url     : https://prove2.me/submissions/00c3b690-eed3-4044-ab46-a5bc97c95ac5

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreShape
import Theorems.Thm_PositivityTheory_KReal_getD_pad_right

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
theorem _root_.solution (p q r s n m : ℕ) (hq : q ≤ r) (hp : p ≤ s) :
    shiftNu (cPair p q) (laNeg p q r s n m) =
      ofBlocks (pad [] (r - q) (List.replicate q (-(n : ℤ)))) (pad [] (s - p) (List.replicate p (-(m : ℤ)))) := by
  funext x
  rcases x with k | l
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right q r k _ hq k.isLt]
    split_ifs <;> push_cast <;> ring
  · simp only [shiftNu, laNeg, ofBlocks, getD_pad_right p s l _ hp l.isLt]
    split_ifs <;> push_cast <;> ring
end PositivityTheory.KReal
