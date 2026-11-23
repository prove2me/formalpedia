-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.prod_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:03.220983+00:00
-- url     : https://prove2.me/submissions/b276a946-013a-40e9-8ec2-d873a1e364f6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prFst_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_prSnd_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prFst_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.DS.prSnd_apply

set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {x y : WithLp 2 (M₁ × M₂)} (h₁ : prFst x = prFst y) (h₂ : prSnd x = prSnd y) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)
end ReciprocityTheory.ChartRestriction.DS
