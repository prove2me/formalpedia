-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.toMK_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:09:31.420928+00:00
-- url     : https://prove2.me/submissions/e2980e5b-69d2-4491-afea-dd5b38d7a87c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_PolarJmConjTranspose
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toMK_facts

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
variable {n : ℕ}
variable {ε : Fin n → Bool}
open PolarDecomposition
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h1 : toMK k⁻¹ * toMK k = 1 := by
    unfold toMK toM
    simp
  have h2 := (toMK_facts k).2.1
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * (toMK k)ᴴ) := by rw [h2, mul_one]
    _ = (toMK k)ᴴ := by rw [← mul_assoc, h1, one_mul]
end ReciprocityTheory.ChartRestriction.DS.S7
