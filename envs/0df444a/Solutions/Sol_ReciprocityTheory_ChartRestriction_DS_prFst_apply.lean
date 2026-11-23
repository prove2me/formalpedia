-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.prFst_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:59.933101+00:00
-- url     : https://prove2.me/submissions/1bb89aec-03d5-4ac0-a136-a2d0c374a279

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (x : WithLp 2 (M₁ × M₂)) : prFst x = (WithLp.ofLp x).1 := rfl
end ReciprocityTheory.ChartRestriction.DS
