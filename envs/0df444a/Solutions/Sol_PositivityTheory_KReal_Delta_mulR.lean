-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.mulR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:40:29.227947+00:00
-- url     : https://prove2.me/submissions/8f1e5e41-be69-47db-a17a-0c7b49245af6

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
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
namespace PositivityTheory.KReal.Delta
theorem _root_.solution (y : B) (t : A ⊗[ℂ] B) : ((1 : A) ⊗ₜ[ℂ] y) * t = (LinearMap.mulLeft ℂ y).lTensor A t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [mul_add, map_add, ha, hb]
end PositivityTheory.KReal.Delta
