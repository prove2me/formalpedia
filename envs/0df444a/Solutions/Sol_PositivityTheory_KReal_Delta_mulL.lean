-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.mulL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:38.580053+00:00
-- url     : https://prove2.me/submissions/f68525b6-4a06-47b4-b1a7-dfc4e8cc7bda

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
theorem _root_.solution (x : A) (t : A ⊗[ℂ] B) : (x ⊗ₜ[ℂ] (1 : B)) * t = (LinearMap.mulLeft ℂ x).rTensor B t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => rw [mul_add, map_add, ha, hb]
end PositivityTheory.KReal.Delta
