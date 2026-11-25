-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.local_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:25:18.932819+00:00
-- url     : https://prove2.me/submissions/ff691c08-54f3-45c1-a5b9-e8629c9f1762

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_real_bound
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_sqn_s_eq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_zLoc_lower
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_continuous_sqn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_lintegral_chart_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_eq_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_lintegral_ball_rpow_lt_top


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) (hMVI : MVIntStatement n) (hn : 2 ≤ n) {L : La}
    {N : ℕ} {w : Fin N → ι → Y → ℂ} {w0 : ι → Y → ℂ} {s : Fin n → ι → Y → ℂ}
    (hD : A.D0 L w w0 s) {la : La} {f : ι → Y → ℂ} (hf : A.IsSec la f) {T : ℕ}
    (hT : n + 1 ≤ T) {P : Y} (hP : P ∈ A.zeroSet s) (hv : A.VanishOrd f P (T - n)) :
    ∃ U : Set Y, IsOpen U ∧ P ∈ U ∧
      ∫⁻ y in U, ENNReal.ofReal (A.nsq la f y * A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu < ⊤ := by
  set i := A.pick P with hi
  set e := A.chart i with he
  set vP := e P with hvP
  have hPs : P ∈ e.source := A.mem_pick P
  have hvt : vP ∈ e.target := e.map_source hPs
  have htn : e.target ∈ 𝓝 vP := e.open_target.mem_nhds hvt
  have hsymm : ContinuousAt e.symm vP := e.continuousAt_symm hvt
  have hsP : e.symm vP = P := e.left_inv hPs
  have cph : ∀ la' : La, ContinuousAt (fun v => A.ph la' i (e.symm v)) vP := fun la' =>
    (A.smooth_ph la' i).continuousOn.continuousAt htn
  have cw0 : ContinuousAt (fun v => w0 i (e.symm v)) vP := by
    have h := (hD.isSection_denom.1 i).continuousOn
    simp only [Set.preimage_univ, Set.inter_univ] at h
    exact h.continuousAt htn
  obtain ⟨C1, hC1⟩ := hv
  obtain ⟨K3, hK3pos, hK3⟩ := A.zLoc_lower hD (by omega) hP
  set B2 := Real.exp (-A.ph la i P) + 1 with hB2
  have hE2 : ∀ᶠ v in 𝓝 vP, Real.exp (-A.ph la i (e.symm v)) < B2 := by
    have hc : ContinuousAt (fun v => Real.exp (-A.ph la i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph la).neg
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  set g4 : V n → ℝ := fun v => ‖w0 i (e.symm v)‖ ^ 2 * Real.exp (-A.ph L i (e.symm v)) with hg4
  have g4P : 0 < g4 vP := by
    simp only [g4, hsP]
    have := hD.w0_ne P hP
    positivity
  have hE4 : ∀ᶠ v in 𝓝 vP, g4 vP / 2 < g4 v :=
    ((cw0.norm.pow 2).mul (Real.continuous_exp.continuousAt.comp (cph L).neg)).eventually
      (eventually_gt_nhds (half_lt_self g4P))
  set g6 : V n → ℝ := fun v => A.sqn L w (e.symm v) with hg6
  have g6P : 0 < g6 vP := by
    simp only [g6, hsP]
    obtain ⟨k, hk⟩ := hD.no_common_zero P
    have h0 : 0 < A.nsq L (w k) P := by
      unfold nsq
      have := norm_pos_iff.2 hk
      positivity
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq L (w j) P)
      (fun j _ => A.nsq_nonneg L (w j) P) (Finset.mem_univ k))
  have hE6 : ∀ᶠ v in 𝓝 vP, g6 vP / 2 < g6 v :=
    ((A.continuous_sqn hD.sec_w).continuousAt.comp hsymm).eventually
      (eventually_gt_nhds (half_lt_self g6P))
  set B7 := Real.exp (A.ph A.kap i P) + 1 with hB7
  have hE7 : ∀ᶠ v in 𝓝 vP, Real.exp (A.ph A.kap i (e.symm v)) < B7 := by
    have hc : ContinuousAt (fun v => Real.exp (A.ph A.kap i (e.symm v))) vP :=
      Real.continuous_exp.continuousAt.comp (cph A.kap)
    exact hc.eventually (eventually_lt_nhds (by simp only [hsP]; linarith))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1
    ((show ∀ᶠ v in 𝓝 vP, v ∈ e.target from htn).and (hC1.and (hE2.and (hK3.and (hE4.and (hE6.and hE7))))))
  set r := min ε 1 with hr
  set W := Metric.ball vP r with hW
  have hWb : W ⊆ Metric.ball vP ε := Metric.ball_subset_ball (min_le_left _ _)
  have hWt : W ⊆ e.target := fun v hv => (hball v (hWb hv)).1
  have hUo : IsOpen (e.source ∩ e ⁻¹' W) := e.isOpen_inter_preimage Metric.isOpen_ball
  refine ⟨e.source ∩ e ⁻¹' W, hUo, ⟨hPs, Metric.mem_ball_self (lt_min hε one_pos)⟩, ?_⟩
  set c := (g4 vP / 2) / K3 ^ 2 with hc
  have hcpos : 0 < c := by positivity
  set m6 := g6 vP / 2 with hm6
  have hm6pos : 0 < m6 := by positivity
  set K := C1 ^ 2 * B2 * c ^ (-((T : ℝ) - 1 / 2)) * m6 ^ (-(1 / 2 : ℝ)) with hK
  have hB2pos : 0 < B2 := by positivity
  have hKnn : 0 ≤ K := by positivity
  set ψ : V n → ℝ≥0∞ := fun v => ENNReal.ofReal ‖v - vP‖ ^ (-2 * ((n : ℝ) - 1 / 2)) with hψ
  have hψc : Continuous ψ :=
    ENNReal.continuous_rpow_const.comp
      (ENNReal.continuous_ofReal.comp (continuous_norm.comp (continuous_id.sub continuous_const)))
  have hpt : ∀ x ∈ e.source ∩ e ⁻¹' W,
      ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
        A.sqn L w x ^ (-(1 / 2 : ℝ))) ≤ ENNReal.ofReal K * ψ (e x) := by
    rintro x ⟨hxs, hxW⟩
    obtain ⟨-, h1, h2, h3, h4, h6, -⟩ := hball (e x) (hWb hxW)
    have hx : e.symm (e x) = x := e.left_inv hxs
    simp only [g4, g6, hx] at h4 h6
    rw [hx] at h1 h2
    set d := ‖e x - vP‖ with hd
    have hw0 : w0 i x ≠ 0 := by
      intro h
      rw [h, norm_zero] at h4
      have : g4 vP / 2 < 0 := by simpa using h4
      linarith
    have hS : c * d ^ 2 ≤ A.sqn L s x := by
      rw [A.sqn_s_eq hD.sec_s hxs hw0]
      set z := ‖A.zLoc w0 s i (e x)‖
      have hz : d ^ 2 ≤ K3 ^ 2 * z ^ 2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h3 2
      have hc1 : c * d ^ 2 ≤ (g4 vP / 2) * z ^ 2 := by
        rw [hc, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith [g4P]
      exact hc1.trans (mul_le_mul_of_nonneg_right h4.le (sq_nonneg _))
    have hF : A.nsq la f x ≤ (C1 * d ^ (T - n)) ^ 2 * B2 := by
      rw [A.nsq_eq_chart hf hxs]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h1 2) h2.le (Real.exp_pos _).le
        (sq_nonneg _)
    have hR := real_bound (T := T) (n := n) (by omega) (norm_nonneg _) (A.nsq_nonneg la f x) hF
      hB2pos.le hcpos hS hm6pos h6.le
    calc ENNReal.ofReal (A.nsq la f x * A.sqn L s x ^ (-((T : ℝ) - 1 / 2)) *
          A.sqn L w x ^ (-(1 / 2 : ℝ)))
        ≤ ENNReal.ofReal (K * d ^ (-2 * ((n : ℝ) - 1 / 2))) := ENNReal.ofReal_le_ofReal hR
      _ = ENNReal.ofReal K * ENNReal.ofReal (d ^ (-2 * ((n : ℝ) - 1 / 2))) :=
          ENNReal.ofReal_mul hKnn
      _ ≤ ENNReal.ofReal K * ψ (e x) := by
          gcongr
          rcases (norm_nonneg (e x - vP)).eq_or_lt with h0 | hpos
          · rw [← hd] at h0
            rw [← h0, Real.zero_rpow (by
              have : (2:ℝ) ≤ n := by exact_mod_cast hn
              linarith)]
            simp
          · simp only [ψ]
            rw [ENNReal.ofReal_rpow_of_pos hpos]
  have hUm : MeasurableSet (e.source ∩ e ⁻¹' W) := hUo.measurableSet
  calc ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal (A.nsq la f y *
        A.sqn L s y ^ (-((T : ℝ) - 1 / 2)) * A.sqn L w y ^ (-(1 / 2 : ℝ))) ∂A.mu
      ≤ ∫⁻ y in e.source ∩ e ⁻¹' W, ENNReal.ofReal K * ψ (e y) ∂A.mu :=
        setLIntegral_mono' hUm hpt
    _ = ENNReal.ofReal K * ∫⁻ y in e.source ∩ e ⁻¹' W, ψ (e y) ∂A.mu :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal B7 * ∫⁻ v in W, ψ v) := by
        gcongr
        exact A.lintegral_chart_le i P Metric.isOpen_ball hWt _
          (fun v hv => ENNReal.ofReal_le_ofReal (hball v (hWb hv)).2.2.2.2.2.2.le) ψ hψc
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
        exact lintegral_ball_rpow_lt_top hMVI (by omega) vP (min_le_right _ _) (by linarith)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
