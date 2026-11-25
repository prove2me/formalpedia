-- Prove2me | solution 1 for PositivityTheory.KReal.Delta.dl_XR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:27:37.033914+00:00
-- url     : https://prove2.me/submissions/51322c55-196f-4a77-89c2-860a3f2573e0

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
theorem _root_.solution (a : Ix p q) (l : Fin s) :
    dl p q r s (X (a, Sum.inr l)) = (1 : Pol p q r 0) ⊗ₜ[ℂ] (X (a, Sum.inr l) : Pol p q 0 s) := by
  simp [dl, dv]
end PositivityTheory.KReal.Delta
