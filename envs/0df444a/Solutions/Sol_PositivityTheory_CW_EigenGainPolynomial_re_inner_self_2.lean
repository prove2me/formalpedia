-- Prove2me | solution 2 for PositivityTheory.CW.EigenGainPolynomial.re_inner_self
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-23T22:52:50.552436+00:00
-- url     : https://prove2.me/submissions/bfde2b67-9920-4098-8ece-6b679c3c9357

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

theorem solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (w : V) :
    (inner ℂ w w).re = ‖w‖ ^ 2 := by
  exact @inner_self_eq_norm_sq ℂ _ _ _ _ w
