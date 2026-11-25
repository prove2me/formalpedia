-- Prove2me | solution 1 for PositivityTheory.KReal.Harm.hc_hc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:41:22.147311+00:00
-- url     : https://prove2.me/submissions/cd843db1-ea30-4dcc-be58-9acdc205683c

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
theorem _root_.solution (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) = if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)
end PositivityTheory.KReal.Harm
