-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:45.704912+00:00
-- url     : https://prove2.me/submissions/1f7b0d13-e9a7-4f95-8b64-a0a877895241

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM

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
theorem _root_.solution : Continuous fun k : KG ε => toMK k := by
  first
    | fun_prop
    | exact continuous_subtype_val.comp continuous_subtype_val
    | exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    | exact (continuous_subtype_val.comp continuous_subtype_val).comp continuous_subtype_val
    | continuity
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
