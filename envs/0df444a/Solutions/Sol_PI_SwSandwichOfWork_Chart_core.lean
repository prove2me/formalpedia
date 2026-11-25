-- Prove2me | solution 1 for PI.SwSandwichOfWork.Chart_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:39:04.971179+00:00
-- url     : https://prove2.me/submissions/d7a45439-51aa-4c3c-aab3-90e1c921db29

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LongWeylElementSquare
import Definitions.Def_Formalism_PeriodIntegrals_SwSand
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_SandwichOfOfCharts
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_UnrealifyRL
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SandwichChart_ChartZeroEqOneOfLongWeylSq
import Theorems.Thm_PI_SwSandwichOfWork_chart_zero_eq_one_of_longWeylSq
import Theorems.Thm_PI_SwSandwichOfWork_Chart_phi_mem
import Theorems.Thm_PI_SwSandwichOfWork_Chart_norm_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
open Matrix Filter Topology Classical
open scoped ENNReal NNReal
open PI PI.SwSandwichOfWork
open PI.SwBig PI.SwSand
attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra
variable {k r : ℕ}
namespace PI.SwSandwichOfWork
theorem _root_.solution (hN : NormRL) (hLog : LogG) (hW : LongWeylElementSquare) (hBC : BigCellG) (hPF : PhiForm)
    (hPD : PhiDeriv) (hLW : LieWb) (hEN : ExpN) (hLI : LIso) (k r : ℕ) :
    ∃ F : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r → Mat k r, HasStrictFDerivAt F (Lm k r) 0 ∧
      F 0 = 0 ∧ ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Vs k r, ‖v‖ < δ →
        F v ∈ uH k r ∧ NormedSpace.exp (F v) = PhiP k r v ∧ ‖F v - Lm k r v‖ ≤ η * ‖Lm k r v‖ := by
  have hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r)
      ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r ≃L[ℝ] Mat k r) : Mat k r →L[ℝ] Mat k r) 0 :=
    (hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := Mat k r)).congr_fderiv
      (ContinuousLinearMap.ext fun _ => rfl)
  set G := hE.localInverse _ _ _ with hGdef
  have hexp0 : NormedSpace.exp (0 : Mat k r) = 1 := by simp
  have hP : HasStrictFDerivAt (PhiP k r) (Lm k r) 0 := hPD k r
  have hPe : PhiP k r 0 = NormedSpace.exp (0 : Mat k r) := by rw [hexp0]; exact chart_zero_eq_one_of_longWeylSq hW
  have hF : HasStrictFDerivAt (fun v => G (PhiP k r v)) (Lm k r) 0 := by
    have h1 : HasStrictFDerivAt G
        (((ContinuousLinearEquiv.refl ℝ (Mat k r)).symm : Mat k r ≃L[ℝ] Mat k r) : Mat k r →L[ℝ] Mat k r)
        (PhiP k r 0) := by
      rw [hPe]; exact hE.to_localInverse
    exact (h1.comp 0 hP).congr_fderiv (ContinuousLinearMap.ext fun _ => rfl)
  have hF0 : G (PhiP k r 0) = 0 := by rw [hPe]; exact hE.localInverse_apply_image
  have hR : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r),
      NormedSpace.exp (G (PhiP k r v)) = PhiP k r v := by
    have ht : Filter.Tendsto (PhiP k r) (𝓝 0) (𝓝 (NormedSpace.exp (0 : Mat k r))) := by
      rw [← hPe]; exact hP.continuousAt.tendsto
    exact ht.eventually hE.eventually_right_inverse
  obtain ⟨δL, hδL, hLg⟩ := hLog k r
  have hU : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r), ‖G (PhiP k r v)‖ < δL := by
    have ht : Filter.Tendsto (fun v => G (PhiP k r v)) (𝓝 0) (𝓝 0) := by
      have h2 := hF.continuousAt.tendsto
      rwa [hF0] at h2
    exact (Metric.tendsto_nhds.mp ht δL hδL).mono fun v hv => by rwa [dist_zero_right] at hv
  have hB1 : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r), ‖v‖ < 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) one_pos]
      with v hv
    exact mem_ball_zero_iff.mp hv
  refine ⟨fun v => G (PhiP k r v), hF, hF0, fun η hη => ?_⟩
  have hO : ∀ᶠ v in 𝓝 (0 : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r),
      ‖G (PhiP k r v) - Lm k r v‖ ≤ η * ‖v‖ := by
    have h := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hF.hasFDerivAt).def hη
    filter_upwards [h] with v hv
    simp only [zero_add, hF0, sub_zero] at hv
    exact hv
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp (hR.and (hU.and (hB1.and hO)))
  refine ⟨δ, hδ, fun v hv hvn => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hall (show dist v 0 < δ by rwa [dist_zero_right])
  have hx : ‖v.2.1‖ < 1 := lt_of_le_of_lt ((norm_fst_le v.2).trans (norm_snd_le v)) h3
  refine ⟨hLg (G (PhiP k r v)) h2 (by rw [h1]; exact Chart_phi_mem hBC hPF hLW hEN hv hx), h1,
    h4.trans (mul_le_mul_of_nonneg_left (Chart_norm_le hN hLI hv) hη.le)⟩
end PI.SwSandwichOfWork
