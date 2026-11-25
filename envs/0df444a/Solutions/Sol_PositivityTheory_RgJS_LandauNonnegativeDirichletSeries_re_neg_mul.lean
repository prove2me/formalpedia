-- Prove2me | solution 1 for PositivityTheory.RgJS.LandauNonnegativeDirichletSeries.re_neg_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:56:09.009797+00:00
-- url     : https://prove2.me/submissions/88b0c542-89bf-44e5-a670-a89ac7ce4269

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_LandauIteratedDerivatives_LandauL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Filter Topology
open PositivityTheory PositivityTheory.RgJS PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
namespace PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
theorem _root_.solution (l : ℝ) (s : ℂ) : (-(l : ℂ) * s).re = -(l * s.re) := by simp
end PositivityTheory.RgJS.LandauNonnegativeDirichletSeries
