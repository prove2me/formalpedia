-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.continuous_GintD
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:31.264376+00:00
-- url     : https://prove2.me/submissions/5fa3861f-61fb-4b52-ae2b-7e4f6609c644

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuousOn_fderiv_phiP
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK__f840e4671769
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_GintD_apply

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
    (hx : x ∈ Uset ε) : Continuous (GintD T μ x) := by
  refine continuous_clm_apply.mpr fun H => ?_
  have h1 : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  have hA := (continuousOn_fderiv_phiP μ).comp_continuous h1 hx
  have hB : Continuous fun k : KG ε => toMK k⁻¹ * Matrix.of H * toMK k :=
    (continuous_toMK_inv.matrix_mul continuous_const).matrix_mul continuous_toMK'
  have e : (fun k => GintD T μ x k H) = fun k => fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)
      (toMK k⁻¹ * Matrix.of H * toMK k) • (T.op k * projW T * T.op k⁻¹) :=
    funext fun k => GintD_apply T μ k (hx k) H
  rw [e]
  exact (hA.clm_apply hB).smul (continuous_P T)
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
