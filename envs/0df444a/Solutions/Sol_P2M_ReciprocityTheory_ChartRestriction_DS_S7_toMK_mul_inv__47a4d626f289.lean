-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul_inv__47a4d626f289
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:29.311337+00:00
-- url     : https://prove2.me/submissions/f90a7fcb-eefd-4449-8c92-9d220d08345a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ExpInPPosDef
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousConjProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ToMKMulInv
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_mul__88ef2175972f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_toMK_one__42e93fcaad20

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
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (k : KG ε) : toMK k * toMK k⁻¹ = 1 := by rw [← toMK_mul', mul_inv_cancel, toMK_one']
end ReciprocityTheory.ChartRestriction.DS.S7
