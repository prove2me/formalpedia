-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.GintD_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:51.389837+00:00
-- url     : https://prove2.me/submissions/51086889-a010-45be-aadb-ded1a03ea1d6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_Gint0

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
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε)
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) (H : 𝕄) :
    GintD T μ x k H = fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k) (toMK k⁻¹ * Matrix.of H * toMK k) •
      (T.op k * projW T * T.op k⁻¹) := by
  rw [GintD, (hasFDerivAt_Gint0 T μ k hx).fderiv]
  rfl
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
