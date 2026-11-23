-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mem_prodSub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:14:01.502904+00:00
-- url     : https://prove2.me/submissions/2d8905cc-bd0a-4e74-92d8-191402eb5275

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_SchForm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCoreB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFCore

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
theorem _root_.solution {V₁ : Submodule ℂ M₁} {V₂ : Submodule ℂ M₂} {x : WithLp 2 (M₁ × M₂)} :
    x ∈ prodSub V₁ V₂ ↔ prFst x ∈ V₁ ∧ prSnd x ∈ V₂ := Iff.rfl
end ReciprocityTheory.ChartRestriction.DS
