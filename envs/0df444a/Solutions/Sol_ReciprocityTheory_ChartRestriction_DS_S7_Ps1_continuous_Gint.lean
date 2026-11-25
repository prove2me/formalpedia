-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.continuous_Gint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:09.850274+00:00
-- url     : https://prove2.me/submissions/fd1437e6-8c28-4017-aaae-b4299428c39c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuousOn_phiP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK__f840e4671769
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_P

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ}
    (hx : x ∈ Uset ε) : Continuous (Gint T μ x) := by
  have h1 : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  exact ((continuousOn_phiP μ).comp_continuous h1 hx).smul (continuous_P T)
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
