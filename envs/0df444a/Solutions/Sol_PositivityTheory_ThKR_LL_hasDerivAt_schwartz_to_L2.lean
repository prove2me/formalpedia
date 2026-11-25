-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.hasDerivAt_schwartz_to_L2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:19:07.017261+00:00
-- url     : https://prove2.me/submissions/1002fdf6-a063-4e9a-ba90-5043b39e5cc7

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_MetaDef
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_HasDerivAtSchwartzToL2
import Theorems.Thm_PositivityTheory_ThKR_LL_exists_decay
import Theorems.Thm_PositivityTheory_ThKR_LL_csmul
import Theorems.Thm_GlobalTheory_RealWeil_schwartzToL2_apply
import Theorems.Thm_PositivityTheory_ThKF_E_Impl_continuous


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {F : ℝ → Sch l} {G : Sch l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C', hC', hG⟩ := exists_decay G N
  let u : ℝ → Sch l := fun t => (((t - t₀)⁻¹ : ℝ) : ℂ) • (F t - F t₀) - G
  have hu : ∀ t x, u t x = (t - t₀)⁻¹ • (F t x - F t₀ x) - G x := fun t x => by
    simp [u]
  have h1 : Tendsto (fun t => ∫ x, ‖u t x‖ ^ (2 : ℝ)) (𝓝[≠] t₀) (𝓝 (∫ _x : EuclideanSpace ℝ l, (0 : ℝ))) := by
    have hi := (integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := N)
      (by rw [hN]; push_cast; linarith)).const_mul ((C + C') ^ 2)
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun t => ((u t).continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable) ?_ hi
      (.of_forall fun x => ?_)
    · filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with t ht ht0
      refine .of_forall fun x => ?_
      have ht1 : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 ht0)
      have hw : 1 ≤ (1 + ‖x‖) ^ N := one_le_pow₀ (by simp)
      have h2 : (1 + ‖x‖) ^ N * ‖u t x‖ ≤ C + C' := by
        rw [hu]
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
        rw [mul_add, norm_smul, norm_inv, Real.norm_eq_abs]
        refine add_le_add ?_ (hG x)
        rw [mul_left_comm, inv_mul_le_iff₀ ht1, mul_comm |t - t₀|]
        exact ht x
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity),
        ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h3 : ((1 + ‖x‖) ^ N * ‖u t x‖) ^ 2 ≤ (C + C') ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      refine le_trans ?_ h3
      rw [mul_pow, mul_comm]
      gcongr
      nlinarith
    · have h2 := (hasDerivAt_iff_tendsto_slope.1 (hp x))
      have h3 := tendsto_iff_norm_sub_tendsto_zero.1 h2
      have h4 := h3.rpow_const (p := 2) (Or.inr (by norm_num))
      simpa [hu, slope_def_module] using h4
  rw [integral_zero] at h1
  have h2 := h1.rpow_const (p := 2⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr fun t => ?_
  have : slope (fun t => schwartzToL2 l (F t)) t₀ t - schwartzToL2 l G = (u t).toLp 2 volume := by
    rw [← schwartzToL2_apply, slope_def_module]
    simp only [u, map_sub, map_smul]
    simp only [csmul]
  rw [this, norm_toLp' (by simp) (by simp)]
  simp
end PositivityTheory.ThKR.LL
