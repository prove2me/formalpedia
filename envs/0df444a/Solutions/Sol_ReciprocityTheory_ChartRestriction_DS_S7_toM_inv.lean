-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.toM_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:41:40.199577+00:00
-- url     : https://prove2.me/submissions/8cc30437-12cb-4bc9-a0ef-79aae7bcc739

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_left_inv_of_inUJ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (ε : Fin n → Bool) (g : UJ ε) : toM g⁻¹ = Jm ε * (toM g)ᴴ * Jm ε :=
  Units.inv_eq_of_mul_eq_one_left (left_inv_of_inUJ ε _ g.2)
end ReciprocityTheory.ChartRestriction.DS.S7
