-- Prove2me | solution 1 for QnRdSkewW.contOn_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:36.57259+00:00
-- url     : https://prove2.me/submissions/342c69ad-f209-4a4f-9642-7feac96c1ae0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Development
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_HasDerivAtShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
open QnRdSkewW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {X : Matrix (Fin n) (Fin n) ℂ}
namespace QnRdSkewW
theorem _root_.solution {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnSet G f) : ContinuousOn f G := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg₀U, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hg₀U)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hg₀U hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hg₀U), self_mem_nhdsWithin] with g hgU hgG
  exact hfF g hgU hgG
end QnRdSkewW
