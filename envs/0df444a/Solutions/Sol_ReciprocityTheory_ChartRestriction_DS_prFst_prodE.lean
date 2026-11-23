-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.prFst_prodE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:00:01.871106+00:00
-- url     : https://prove2.me/submissions/357b38d8-604b-400e-be24-a1183a83ca03

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
variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prFst (prodE E₁ E₂ a b x) = E₁ a b (prFst x) := rfl
end ReciprocityTheory.ChartRestriction.DS
