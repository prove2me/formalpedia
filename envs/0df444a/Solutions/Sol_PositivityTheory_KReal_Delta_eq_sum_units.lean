-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.eq_sum_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:55.824969+00:00
-- url     : https://prove2.me/submissions/e40f7814-f8b2-46a9-886e-18d94bb970ef

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta

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
open scoped InnerProductSpace TensorProduct
open PositivityTheory PositivityTheory.KReal
open PositivityTheory.KReal.Delta
variable {p q r s : ℕ}
namespace PositivityTheory.KReal.Delta
theorem _root_.solution (Z : Mat p q) : Z = ∑ a, ∑ b, Z a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ext i j
  simp [Eab, Matrix.single_apply]
end PositivityTheory.KReal.Delta
