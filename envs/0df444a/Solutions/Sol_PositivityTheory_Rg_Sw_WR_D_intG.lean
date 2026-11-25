-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.WR.D.intG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:30:03.813164+00:00
-- url     : https://prove2.me/submissions/e4c42444-fb7f-4210-a03f-b9954452c9a7

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_DensDefs
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsBisMore
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MollifiedIntegrability_ContinuousEvXI
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_evXI
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_continuous_gs
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_evX_bound
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_norm_gs_le
import Theorems.Thm_PositivityTheory_Rg_Sw_WR_D_decay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.D
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.WR.D
theorem _root_.solution : IntG := by
  intro m n c hc P
  obtain ⟨C, d, hP⟩ := evX_bound P
  set r : ℕ := Module.finrank ℝ (Fin m → Fin n → ℂ) + 1 with hr
  obtain ⟨K, hK⟩ := decay c hc (d + r)
  have hint : Integrable (fun x : Fin m → Fin n → ℂ => (1 + ‖x‖) ^ (-(r : ℝ))) :=
    integrable_one_add_norm (by rw [hr]; push_cast; linarith)
  refine (hint.const_mul (|C| * K)).mono' ((continuous_evXI P).mul (continuous_gs c)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hpos : 0 < 1 + ‖x‖ := by linarith
  have hK' : (1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2)) ≤ K :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h1 (by omega)) (Real.exp_pos _).le).trans
      (hK ‖x‖ (norm_nonneg x))
  have hrp : (1 + ‖x‖) ^ (-(r : ℝ)) = ((1 + ‖x‖) ^ r)⁻¹ := by
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
  have hPx : ‖evX P x‖ ≤ |C| * (1 + ‖x‖) ^ d :=
    (hP x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have hr0 : 0 < (1 + ‖x‖) ^ r := pow_pos hpos r
  rw [norm_mul, hrp]
  calc ‖evX P x‖ * ‖gs c x‖ ≤ (|C| * (1 + ‖x‖) ^ d) * Real.exp (-(c * ‖x‖ ^ 2)) :=
        mul_le_mul hPx (norm_gs_le c hc x) (norm_nonneg _) (by positivity)
    _ = |C| * ((1 + ‖x‖) ^ (d + r) * Real.exp (-(c * ‖x‖ ^ 2))) * ((1 + ‖x‖) ^ r)⁻¹ := by
        rw [pow_add]; field_simp
    _ ≤ |C| * K * ((1 + ‖x‖) ^ r)⁻¹ := by
        gcongr
end PositivityTheory.Rg.Sw.WR.D
