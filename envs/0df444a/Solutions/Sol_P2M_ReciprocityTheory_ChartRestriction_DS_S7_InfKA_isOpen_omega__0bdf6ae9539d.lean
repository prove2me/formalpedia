-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_isOpen_omega__0bdf6ae9539d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:29.969441+00:00
-- url     : https://prove2.me/submissions/3633b62d-84b9-49d8-a7e5-1d3056a06cb5

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_contDiff_lead

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
open scoped ComplexOrder ContDiff ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}
open ReciprocityTheory.ChartRestriction.DS.S7.InfKA
namespace ReciprocityTheory.ChartRestriction.DS.S7.InfKA
theorem _root_.solution : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  first
  | exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const
  | exact isOpen_iInter fun i => isOpen_ne_fun (contDiff_lead _).continuous continuous_const
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
