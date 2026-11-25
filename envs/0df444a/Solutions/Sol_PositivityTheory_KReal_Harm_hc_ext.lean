-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.hc_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:50:34.167205+00:00
-- url     : https://prove2.me/submissions/2a2b9f2e-3dcd-4b9d-b268-515b9c6b8c3f

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLie
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreHarm

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
open PositivityTheory.KReal.Harm
variable {σ : Type}
namespace PositivityTheory.KReal.Harm
theorem _root_.solution {P Q : MvPolynomial σ ℂ} (h : ∀ d, homogeneousComponent d P = homogeneousComponent d Q) : P = Q := by
  ext m
  have := congrArg (coeff m) (h m.degree)
  simpa [coeff_homogeneousComponent] using this
end PositivityTheory.KReal.Harm
