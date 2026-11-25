-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefIntCpt_toE_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:47.652364+00:00
-- url     : https://prove2.me/submissions/04758141-b0ab-4a19-b21f-dfdb300e3a8e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrableOfDecayVG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntCpt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ} {ε : Fin n → Bool}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (n : ℕ) :
    Continuous (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)) := by
  exact (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional
end ReciprocityTheory.ChartRestriction.DS
