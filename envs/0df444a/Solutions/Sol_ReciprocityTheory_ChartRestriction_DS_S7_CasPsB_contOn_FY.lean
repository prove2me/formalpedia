-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.CasPsB.contOn_FY
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:57:14.728627+00:00
-- url     : https://prove2.me/submissions/b03f6d91-035e-45ca-aa65-81a3a71d1bbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuousOn_DPhi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_continuousOn_D2Phi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_CasPsB_FY_facts
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK__f840e4671769
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_P
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_conj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_Ps1_continuous_toMK_inv


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
    {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hΩ : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n) :
    ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => FY T μ Y p.1 p.2) (U ×ˢ Set.univ) ∧
      ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => FY' T μ Y p.1 p.2) (U ×ˢ Set.univ) := by
  have hmaps : Set.MapsTo (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε => toMK p.2⁻¹ * p.1 * toMK p.2)
      (U ×ˢ Set.univ) (OmegaSet n) := fun p hp => hΩ p.1 hp.1 p.2
  have hA : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      fderiv ℂ (Ps1.PhiP μ) (toMK p.2⁻¹ * p.1 * toMK p.2)) (U ×ˢ Set.univ) :=
    (continuousOn_DPhi μ).comp Ps1.continuous_conj.continuousOn hmaps
  have hA2 : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      fderiv ℂ (fderiv ℂ (Ps1.PhiP μ)) (toMK p.2⁻¹ * p.1 * toMK p.2)) (U ×ˢ Set.univ) :=
    (continuousOn_D2Phi μ).comp Ps1.continuous_conj.continuousOn hmaps
  have hP : ContinuousOn (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      T.op p.2 * projW T * T.op p.2⁻¹) (U ×ˢ Set.univ) :=
    ((Ps1.continuous_P T).comp continuous_snd).continuousOn
  have hcY : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      toMK p.2⁻¹ * Y * A * toMK p.2) := fun A =>
    (((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      continuous_const).matrix_mul (Ps1.continuous_toMK'.comp continuous_snd)
  have hcYx : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      toMK p.2⁻¹ * Y * p.1 * toMK p.2) :=
    (((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      continuous_fst).matrix_mul (Ps1.continuous_toMK'.comp continuous_snd)
  have hcH : ∀ A : Matrix (Fin n) (Fin n) ℂ, Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × KG ε =>
      toMK p.2⁻¹ * A * toMK p.2) := fun A =>
    ((Ps1.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (Ps1.continuous_toMK'.comp continuous_snd)
  refine ⟨(hA.clm_apply hcYx.continuousOn).smul hP, ?_⟩
  refine continuousOn_clm_apply.mpr fun H => ?_
  refine (((hA.clm_apply (hcY (Matrix.of H)).continuousOn).add
    ((hA2.clm_apply (hcH (Matrix.of H)).continuousOn).clm_apply hcYx.continuousOn)).smul hP).congr ?_
  intro p hp
  exact (FY_facts T μ Y p.2 (hΩ p.1 hp.1 p.2)).2 H
end ReciprocityTheory.ChartRestriction.DS.S7.CasPsB
