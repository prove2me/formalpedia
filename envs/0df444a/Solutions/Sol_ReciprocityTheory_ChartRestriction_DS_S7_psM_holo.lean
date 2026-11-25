-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.psM_holo
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:57:35.596849+00:00
-- url     : https://prove2.me/submissions/715a0154-9792-440e-9967-c89158d0e90f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_KFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiFacts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_isOpen_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_posSet_subset_Uset
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_GintD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_integrable_GintD
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_hasFDerivAt_psM
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_compactSpace_KG


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
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧
      (∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) ∧
      DifferentiableOn ℂ (psM T μ) U ∧
      ∀ z ∈ U, ∀ H : Matrix (Fin n) (Fin n) ℂ, fderiv ℂ (psM T μ) z H =
        ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, fderiv ℂ (PhiM μ) (toMK k⁻¹ * z * toMK k) (toMK k⁻¹ * H * toMK k) •
            (T.op k * projW T * T.op k⁻¹) ∂(muK ε) := by
  have := compactSpace_KG ε
  refine ⟨Ps1.Uset ε, Ps1.isOpen_Uset, Ps1.posSet_subset_Uset, fun z hz k => hz k,
    fun z hz => ?_, fun z hz H => ?_⟩
  · have h : DifferentiableAt ℂ (psM T μ) z := (Ps1.hasFDerivAt_psM T μ hz).differentiableAt
    exact h.differentiableWithinAt
  · rw [show fderiv ℂ (psM T μ) z H =
        fderiv ℂ (fun x : Fin n → Fin n → ℂ => psM T μ x) z (Matrix.of.symm H) from rfl,
      (Ps1.hasFDerivAt_psM T μ hz).fderiv, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.integral_apply (Ps1.integrable_GintD T μ hz)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    exact Ps1.GintD_apply T μ k (hz k) (Matrix.of.symm H)
end ReciprocityTheory.ChartRestriction.DS.S7
