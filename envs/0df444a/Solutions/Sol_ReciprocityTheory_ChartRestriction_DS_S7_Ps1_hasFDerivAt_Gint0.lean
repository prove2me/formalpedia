-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.Ps1.hasFDerivAt_Gint0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:01.774093+00:00
-- url     : https://prove2.me/submissions/38fbaf6a-d141-4955-87c2-11ef9d647a9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_contDiffAt_phiP

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
    (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => Gint T μ y k)
      (((fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)).comp (conjCLM (toMK k⁻¹) (toMK k))).smulRight
        (T.op k * projW T * T.op k⁻¹)) x := by
  have h1 : HasFDerivAt (fun y : 𝕄 => toMK k⁻¹ * Matrix.of y * toMK k)
      (conjCLM (toMK k⁻¹) (toMK k)) x :=
    (conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
  have h2 : HasFDerivAt (PhiP μ) (fderiv ℂ (PhiP μ) (toMK k⁻¹ * x * toMK k)) (toMK k⁻¹ * x * toMK k) :=
    (contDiffAt_phiP μ hx).differentiableAt_one.hasFDerivAt
  exact (h2.comp x h1).smul_const (T.op k * projW T * T.op k⁻¹)
end ReciprocityTheory.ChartRestriction.DS.S7.Ps1
