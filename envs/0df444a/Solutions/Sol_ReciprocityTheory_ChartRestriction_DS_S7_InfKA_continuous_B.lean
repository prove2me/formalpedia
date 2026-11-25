-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.InfKA.continuous_B
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:24:53.146497+00:00
-- url     : https://prove2.me/submissions/ca5257c2-2607-4bb9-90e9-1d24dd22542b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ByParts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DTauFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DerivGA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiM
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK__342259628be7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_InfKA_continuous_toMK_inv

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
theorem _root_.solution (A : Matrix (Fin n) (Fin n) ℂ) : Continuous fun k : KG ε => toMK k⁻¹ * A * toMK k := by
  first
    | exact (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
    | exact ((continuous_toMK_inv (ε := ε)).mul continuous_const).mul continuous_toMK'
end ReciprocityTheory.ChartRestriction.DS.S7.InfKA
