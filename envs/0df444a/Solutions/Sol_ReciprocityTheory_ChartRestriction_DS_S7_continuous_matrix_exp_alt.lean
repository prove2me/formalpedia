-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.continuous_matrix_exp_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:53.739359+00:00
-- url     : https://prove2.me/submissions/2eb70dde-fb2c-4e18-bc07-ec5f66f361c7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_LocalA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Filter Topology
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous
end ReciprocityTheory.ChartRestriction.DS.S7
