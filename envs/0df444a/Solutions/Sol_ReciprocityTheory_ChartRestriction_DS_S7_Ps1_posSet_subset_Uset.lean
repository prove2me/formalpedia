-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.posSet_subset_Uset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:54:47.758487+00:00
-- url     : https://prove2.me/submissions/d1e05751-b826-4deb-9719-3828f4fc2b46

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_toMK_inv_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_posSet_subset_omega


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
open ReciprocityTheory.ChartRestriction.DS.S7.Ps1
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.Ps1
theorem _root_.solution : posSet n ⊆ Uset ε := by
  intro x hx k
  apply posSet_subset_omega
  show (toMK k⁻¹ * x * toMK k).PosDef
  rw [toMK_inv_eq]
  refine Matrix.PosDef.conjTranspose_mul_mul_same hx ?_
  intro v w hvw
  have h1 : (toMK k)ᴴ * toMK k = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem k.2.1
  have := congrArg (fun u => (toMK k)ᴴ *ᵥ u) hvw
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] using this
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
