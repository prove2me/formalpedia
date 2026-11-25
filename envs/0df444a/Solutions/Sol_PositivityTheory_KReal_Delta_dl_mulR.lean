-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.dl_mulR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:58:32.458983+00:00
-- url     : https://prove2.me/submissions/a005f2b4-0886-44da-8c4f-e195c2aba0aa

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Theorems.Thm_PositivityTheory_KReal_Delta_mulR
import Theorems.Thm_PositivityTheory_KReal_Delta_dl_XR

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
theorem _root_.solution (a : Ix p q) (l : Fin s) (f : Pol p q r s) :
    dl p q r s (X (a, Sum.inr l) * f) =
      (LinearMap.mulLeft ℂ (X (a, Sum.inr l) : Pol p q 0 s)).lTensor _ (dl p q r s f) := by
  rw [map_mul, dl_XR, mulR]
end PositivityTheory.KReal.Delta
