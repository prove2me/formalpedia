-- Prove2me | solution 1 for PositivityTheory.KReal.twAct_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:22:04.158831+00:00
-- url     : https://prove2.me/submissions/a0a34a99-aa4e-4494-a4ce-807080050d6e

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_TensorIrr
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockHarmSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockJointMult
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockOneDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockWtDeg
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDefs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action
open scoped InnerProductSpace
open PositivityTheory PositivityTheory.KReal
namespace PositivityTheory.KReal
theorem _root_.solution (p q r s : ℕ) (τ : ℂ) (W : Mat r s) (f : Pol p q r s) :
    twAct p q r s τ W f = fockAct2 p q r s W f + (τ * W.trace) • f := by
  simp [twAct]
end PositivityTheory.KReal
