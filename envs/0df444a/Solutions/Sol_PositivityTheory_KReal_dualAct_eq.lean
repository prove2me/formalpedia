-- Prove2me | solution 1 for PositivityTheory.KReal.dualAct_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:46:40.326339+00:00
-- url     : https://prove2.me/submissions/d3b4cd31-c90e-4467-8b82-84e3ef1082ab

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreGraph
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreDelta
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreProj
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreNonv

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
variable {p q : ℕ}
namespace PositivityTheory.KReal
theorem _root_.solution {B : Type} [AddCommGroup B] [Module ℂ B] (ρ : Mat p q →ₗ[ℂ] Module.End ℂ B) (c : ℂ)
    (Z : Mat p q) : dualAct ρ c Z = (c * Z.trace) • (1 : Module.End ℂ B) - ρ (thetaM p q Z) := by
  simp [dualAct]
end PositivityTheory.KReal
