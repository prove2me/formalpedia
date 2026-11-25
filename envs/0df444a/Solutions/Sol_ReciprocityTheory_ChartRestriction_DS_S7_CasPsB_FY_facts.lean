-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.FY_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:50:09.491209+00:00
-- url     : https://prove2.me/submissions/048668bb-fa69-48f9-9226-d96f17c072fa

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_hasFDerivAt_DPhi

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
local notation "𝕄" => Fin n → Fin n → ℂ
variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}
namespace ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
theorem _root_.solution (T : KType ε Λ) (μ : Fin n → ℤ) (Y : Matrix (Fin n) (Fin n) ℂ)
    {x : Matrix (Fin n) (Fin n) ℂ} (k : KG ε) (hx : toMK k⁻¹ * x * toMK k ∈ OmegaSet n) :
    HasFDerivAt (fun y : 𝕄 => FY T μ Y y k) (FY' T μ Y x k) x ∧
      ∀ H : 𝕄, FY' T μ Y x k H =
        (fderiv ℂ (Ps1.PhiP μ) (Matrix.of.symm (toMK k⁻¹ * x * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Y * Matrix.of H * toMK k)) +
          fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) (Matrix.of.symm (toMK k⁻¹ * x * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Matrix.of H * toMK k))
            (Matrix.of.symm (toMK k⁻¹ * Y * x * toMK k))) • (T.op k * projW T * T.op k⁻¹) := by
  have h1 : HasFDerivAt (fun y : 𝕄 => toMK k⁻¹ * Matrix.of y * toMK k)
      (Ps1.conjCLM (toMK k⁻¹) (toMK k)) x :=
    (Ps1.conjCLM (toMK k⁻¹) (toMK k)).hasFDerivAt
  have h2 : HasFDerivAt (fderiv ℂ (Ps1.PhiP μ))
      (fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) (toMK k⁻¹ * x * toMK k)) (toMK k⁻¹ * x * toMK k) :=
    hasFDerivAt_DPhi μ hx
  have h4 : HasFDerivAt (fun y : 𝕄 => toMK k⁻¹ * Y * Matrix.of y * toMK k)
      (Ps1.conjCLM (toMK k⁻¹ * Y) (toMK k)) x :=
    (Ps1.conjCLM (toMK k⁻¹ * Y) (toMK k)).hasFDerivAt
  have h := ((h2.comp x h1).clm_apply h4).smul_const (T.op k * projW T * T.op k⁻¹)
  have hd : HasFDerivAt (fun y : 𝕄 => FY T μ Y y k) _ x := h
  refine ⟨hd.differentiableAt.hasFDerivAt, fun H => ?_⟩
  rw [FY', hd.fderiv]
  all_goals rfl
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
