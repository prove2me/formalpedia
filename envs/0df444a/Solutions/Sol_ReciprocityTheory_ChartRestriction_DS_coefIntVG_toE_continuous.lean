-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.coefIntVG_toE_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:20:54.845694+00:00
-- url     : https://prove2.me/submissions/364b2dfd-218b-4722-8f90-eaf323137948

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IntegrVGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefOp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_CoefIntVG

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
