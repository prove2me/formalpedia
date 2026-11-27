-- Prove2me | solution 1 for PositivityTheory.RgJS.removable_singularity_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:22:13.101101+00:00
-- url     : https://prove2.me/submissions/8640e30d-45e3-4556-ad8d-a08dc38a12d8

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_NewtonLow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_JacquetShalikaBounds_AbsoluteRigidity_RemovableSingularities_RemovableSingularityHolds
import Theorems.Thm_PositivityTheory_RgJS_RemovableSingularityAlt_analytic_D
import Theorems.Thm_PositivityTheory_RgJS_RemovableSingularityAlt_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open PositivityTheory PositivityTheory.RgJS
open RemovableSingularityAlt
namespace PositivityTheory.RgJS
theorem _root_.solution : Remov := by
  intro G r M hG hM
  have han := analytic_D hG
  have key : ∀ j ≤ r, ∀ i < j, D G i 1 = 0 := by
    intro j
    induction j with
    | zero => intro _ i hi; omega
    | succ j ih =>
      intro hj i hi
      have hprev := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact hprev i hi
      ·
        have hfac := factor G i hprev
        have hc : ContinuousAt (D G i) 1 := by
          have := (han i 1 one_pos).continuousAt
          simpa using this

        have hb : ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ‖D G i σ‖ ≤ |M| * (σ - 1) := by
          intro σ h1 h2
          have h0 : (0 : ℝ) < σ - 1 := by linarith
          have hle := hM σ h1 h2
          rw [hfac, norm_mul, norm_pow, show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_of_nonneg h0.le] at hle
          have hpow : (σ - 1) ^ r = (σ - 1) ^ i * (σ - 1) ^ (r - i) := by
            rw [← pow_add]; congr 1; omega
          rw [hpow] at hle
          have hpi : 0 < (σ - 1) ^ i := pow_pos h0 i
          have h3 : ‖D G i σ‖ ≤ M * (σ - 1) ^ (r - i) := by
            have := le_of_mul_le_mul_left (by linarith [hle] : (σ - 1) ^ i * ‖D G i σ‖ ≤ (σ - 1) ^ i * (M * (σ - 1) ^ (r - i))) hpi
            exact this
          have h4 : (σ - 1) ^ (r - i) ≤ σ - 1 := by
            have hr : 1 ≤ r - i := by omega
            calc (σ - 1) ^ (r - i) ≤ (σ - 1) ^ 1 := pow_le_pow_of_le_one h0.le (by linarith) hr
              _ = σ - 1 := pow_one _
          calc ‖D G i σ‖ ≤ M * (σ - 1) ^ (r - i) := h3
            _ ≤ |M| * (σ - 1) ^ (r - i) := mul_le_mul_of_nonneg_right (le_abs_self M) (by positivity)
            _ ≤ |M| * (σ - 1) := mul_le_mul_of_nonneg_left h4 (abs_nonneg M)

        have hlim : Tendsto (fun σ : ℝ => D G i σ) (𝓝[>] 1) (𝓝 (D G i 1)) := by
          have hcr : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
            have := (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left
              (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
            simpa using this
          exact hc.tendsto.comp hcr
        have hlim0 : Tendsto (fun σ : ℝ => D G i σ) (𝓝[>] 1) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero' (g := fun σ : ℝ => |M| * (σ - 1)) (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
          · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with σ hσ
            exact hb σ hσ.1 hσ.2.le
          · have : Tendsto (fun σ : ℝ => |M| * (σ - 1)) (𝓝 1) (𝓝 (|M| * (1 - 1))) :=
              (continuous_const.mul (continuous_id.sub continuous_const)).tendsto 1
            rw [sub_self, mul_zero] at this
            exact this.mono_left nhdsWithin_le_nhds
        exact tendsto_nhds_unique hlim hlim0
  refine ⟨D G r, han r, fun σ _ => factor G r (key r le_rfl) σ⟩
end PositivityTheory.RgJS
