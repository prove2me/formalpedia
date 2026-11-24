-- Prove2me | solution 1 for PositivityTheory.CW.EigenGainPolynomial.re_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:36.023971+00:00
-- url     : https://prove2.me/submissions/3609eb52-cd61-4450-91e8-4261af6102db

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_BasisFormSumOfGain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.EigenGainPolynomial
namespace PositivityTheory.CW.EigenGainPolynomial
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  have := inner_self_eq_norm_sq (𝕜 := ℂ) w
  simpa using this
end PositivityTheory.CW.EigenGainPolynomial
