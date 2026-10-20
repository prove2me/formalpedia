-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P12.thermalEntropy_difference_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T01:16:27.898954+00:00
-- url     : https://prove2.me/submissions/ef80db42-3817-4c17-8fd2-e8512fea69ff

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P12

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Frontier18 QAlgorithms.Papers.Independent.Frontier18.P12

open Filter

open QAlgorithms.Papers.Independent.Information100.P54 (thermalEntropy)

open scoped Topology

theorem g52d_te {x : ℝ} (hx : 0 < x) :
    thermalEntropy x = (Real.log (x + 1) + x * Real.log (1 + 1 / x)) / Real.log 2 := by
  unfold thermalEntropy
  have h : Real.log (1 + 1 / x) = Real.log (x + 1) - Real.log x := by
    rw [show (1:ℝ) + 1 / x = (x + 1) / x by field_simp,
      Real.log_div (by positivity) hx.ne']
  rw [h]; ring

theorem g52d_A : Tendsto (fun x : ℝ => x * Real.log (1 + 1 / x)) atTop (nhds 1) :=
  Real.tendsto_mul_log_one_add_div_atTop 1

theorem g52d_lim (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun G : ℝ => thermalEntropy (a * G + c) - thermalEntropy (b * G + d)) atTop
      (nhds (Real.logb 2 (a / b))) := by
  have t1 : Tendsto (fun G : ℝ => a * G + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_id.const_mul_atTop ha)
  have t2 : Tendsto (fun G : ℝ => b * G + d) atTop atTop :=
    tendsto_atTop_add_const_right _ d (tendsto_id.const_mul_atTop hb)
  have hA1 := g52d_A.comp t1
  have hA2 := g52d_A.comp t2
  have hinv := tendsto_inv_atTop_zero (𝕜 := ℝ)
  have hq : Tendsto (fun G : ℝ => (a + (c + 1) * G⁻¹) / (b + (d + 1) * G⁻¹)) atTop
      (nhds ((a + (c + 1) * 0) / (b + (d + 1) * 0))) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)) (by simp; linarith)
  have hlog := hq.log (by simp; exact ⟨ha.ne', hb.ne'⟩)
  have hF := ((hlog.add hA1).sub hA2).div_const (Real.log 2)
  have hlim : (Real.log ((a + (c + 1) * 0) / (b + (d + 1) * 0)) + 1 - 1) / Real.log 2 =
      Real.logb 2 (a / b) := by
    simp [Real.logb]
  rw [hlim] at hF
  refine hF.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ), t1.eventually_gt_atTop 0,
    t2.eventually_gt_atTop 0] with G hG h1 h2
  simp only [Function.comp]
  rw [g52d_te h1, g52d_te h2]
  have hG' : G ≠ 0 := hG.ne'
  have e : (a + (c + 1) * G⁻¹) / (b + (d + 1) * G⁻¹) = (a * G + c + 1) / (b * G + d + 1) := by
    rw [show a + (c + 1) * G⁻¹ = (a * G + c + 1) / G by field_simp; ring,
      show b + (d + 1) * G⁻¹ = (b * G + d + 1) / G by field_simp; ring,
      div_div_div_cancel_right₀ hG']
  rw [e, Real.log_div (by linarith) (by linarith)]
  ring

theorem g52d_cont : Continuous thermalEntropy := by
  unfold thermalEntropy
  exact ((Real.continuous_mul_log.comp (continuous_add_right 1)).sub
    Real.continuous_mul_log).div_const _

theorem g52d_deriv {x : ℝ} (hx : 0 < x) :
    HasDerivAt thermalEntropy (((Real.log (x + 1) + 1) * 1 - (Real.log x + 1)) / Real.log 2) x := by
  have h1 := (Real.hasDerivAt_mul_log (by linarith : x + 1 ≠ 0)).comp x
    ((hasDerivAt_id x).add_const 1)
  have h2 := Real.hasDerivAt_mul_log hx.ne'
  unfold thermalEntropy
  exact (h1.sub h2).div_const (Real.log 2)

theorem g52d_key {x l : ℝ} (hx : 0 < x) (hl0 : 0 < l) (hl1 : l ≤ 1) :
    l * (Real.log (l * x + 1) - Real.log (l * x)) ≤ Real.log (x + 1) - Real.log x := by
  have hp : 0 < (l * x + 1) / (l * x) := by positivity
  have hg := Real.geom_mean_le_arith_mean2_weighted hl0.le (by linarith : (0:ℝ) ≤ 1 - l)
    hp.le zero_le_one (by ring)
  rw [Real.one_rpow, mul_one] at hg
  have hr : l * ((l * x + 1) / (l * x)) + (1 - l) * 1 = (x + 1) / x := by
    field_simp; ring
  rw [hr] at hg
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hp l) hg
  rw [Real.log_rpow hp, Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) hx.ne'] at hlog
  exact hlog

/-- Monotonic thermal-entropy difference and its limit, arXiv:1503.08139v2,
PDF p.28, the paragraph preceding and including (7.18). Both monotonicity and the
limit are included, for every lambda in [0,1].
Printed: a real `log(1/lambda)` limit also at lambda = 0. Changed: retain that
finite base-2 limit for positive lambda, and state divergence to positive infinity
at lambda = 0. Why: the printed real expression is undefined there, whereas
`g(x) - g(0)` diverges; Lean's division-by-zero default must not replace it.
At lambda = 1 the function is constant, so “increasing” means nondecreasing.
Independent moderation of the endpoint interpretation remains pending. -/
theorem solution (lambda : ℝ)
    (hlower : 0 ≤ lambda) (hupper : lambda ≤ 1) :
    MonotoneOn (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
      (Set.Ici 0) ∧
    (0 < lambda →
      Tendsto (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
        atTop (𝓝 (Real.logb 2 (1 / lambda)))) ∧
    (lambda = 0 →
      Tendsto (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
        atTop atTop) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, fun hl => ?_, fun hl => ?_⟩
  · have hcF : ContinuousOn (fun x : ℝ => thermalEntropy x - thermalEntropy (lambda * x))
        (Set.Ici 0) :=
      (g52d_cont.sub (g52d_cont.comp (continuous_const.mul continuous_id))).continuousOn
    rcases eq_or_lt_of_le hlower with h0 | hpos
    · subst h0
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcF
        (f' := fun x => ((Real.log (x + 1) + 1) * 1 - (Real.log x + 1)) / Real.log 2) ?_ ?_
      · intro x hx
        rw [interior_Ici] at hx
        have := (g52d_deriv hx).sub_const (thermalEntropy (0 * x))
        simp only [zero_mul] at this ⊢
        exact this.hasDerivWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        apply div_nonneg _ hl2.le
        have := Real.log_le_log hx (by linarith : x ≤ x + 1)
        linarith
    · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcF
        (f' := fun x => ((Real.log (x + 1) + 1) * 1 - (Real.log x + 1)) / Real.log 2 -
          ((Real.log (lambda * x + 1) + 1) * 1 - (Real.log (lambda * x) + 1)) / Real.log 2 *
            (lambda * 1)) ?_ ?_
      · intro x hx
        rw [interior_Ici] at hx
        have hlx : 0 < lambda * x := mul_pos hpos hx
        have := (g52d_deriv hx).sub ((g52d_deriv hlx).comp x ((hasDerivAt_id x).const_mul lambda))
        exact this.hasDerivWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        have hk := g52d_key hx hpos hupper
        have : ((Real.log (x + 1) + 1) * 1 - (Real.log x + 1)) / Real.log 2 -
            ((Real.log (lambda * x + 1) + 1) * 1 - (Real.log (lambda * x) + 1)) / Real.log 2 *
              (lambda * 1) =
            ((Real.log (x + 1) - Real.log x) -
              lambda * (Real.log (lambda * x + 1) - Real.log (lambda * x))) / Real.log 2 := by
          field_simp; ring
        rw [this]
        exact div_nonneg (by linarith) hl2.le
  · have h := g52d_lim 1 lambda 0 0 one_pos hl
    refine h.congr (fun G => ?_)
    simp
  · subst hl
    have hlog : Tendsto (fun N : ℝ => Real.log (N + 1) / Real.log 2) atTop atTop :=
      (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_id)).atTop_div_const hl2
    refine tendsto_atTop_mono' _ ?_ hlog
    filter_upwards [eventually_gt_atTop (0:ℝ)] with N hN
    have h0 : thermalEntropy (0 * N) = 0 := by simp [thermalEntropy]
    simp only [h0, sub_zero]
    rw [g52d_te hN]
    apply div_le_div_of_nonneg_right _ hl2.le
    have : 0 ≤ N * Real.log (1 + 1 / N) :=
      mul_nonneg hN.le (Real.log_nonneg (by have := one_div_pos.mpr hN; linarith))
    linarith


end

