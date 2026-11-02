-- Prove2me | solution 1 for RotationContagion.Rotation.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T09:56:20.820193+00:00
-- url     : https://prove2.me/submissions/b1f8c820-1a24-48d2-b02d-a76ee435c380

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model
import Theorems.Thm_RotationContagion_Rotation_loss_ode

open MeasureTheory Set Filter Topology Asymptotics

namespace RotContLemma1

open RotationContagion.Rotation

lemma loss_mem (P : Params) (x : ℝ) : loss P x ∈ Icc (0:ℝ) 1 := by
  unfold loss
  have h := Real.exp_pos (P.γ * (x - b P))
  constructor
  · positivity
  · rw [div_le_one (by linarith)]; linarith

lemma ii_of_bdd (g : ℝ → ℝ) (hg : Measurable g) (hb : ∀ s, g s ∈ Icc (0:ℝ) 1) (a c : ℝ) :
    IntervalIntegrable g volume a c := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := 1) ?_ hg.aestronglyMeasurable ?_
  · exact ((measure_mono Set.uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne
  · exact Eventually.of_forall fun s => by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb s).1, (hb s).2]

/-- chain rule in integral form for `L ∘ E`, `E t = ∫_{t0}^t g`, with `g` bounded measurable. -/
lemma key_deriv (L h : ℝ → ℝ) (hL : ∀ x, HasDerivAt L (h x) x) (hh : Continuous h)
    (g : ℝ → ℝ) (hb : ∀ s, g s ∈ Icc (0:ℝ) 1)
    (hii : ∀ a c, IntervalIntegrable g volume a c) (t0 : ℝ) :
    ∀ t, L (∫ s in t0..t, g s) = L 0 + ∫ s in t0..t, g s * h (∫ u in t0..s, g u) := by
  set E : ℝ → ℝ := fun t => ∫ s in t0..t, g s with hE
  have hEc : Continuous E := intervalIntegral.continuous_primitive hii t0
  have hhE : Continuous (fun s => h (E s)) := hh.comp hEc
  have hii2 : ∀ a c, IntervalIntegrable (fun s => g s * h (E s)) volume a c :=
    fun a c => (hii a c).mul_continuousOn hhE.continuousOn
  have hLc : Continuous L := continuous_iff_continuousAt.2 fun x => (hL x).continuousAt
  set Φ : ℝ → ℝ := fun t => L (E t) - ∫ s in t0..t, g s * h (E s) with hΦ
  have hEsub : ∀ x y, E y - E x = ∫ s in x..y, g s := fun x y =>
    intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)
  have hlip : ∀ x y, |E y - E x| ≤ |y - x| := by
    intro x y
    rw [hEsub]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := y) (C := 1)
      (f := g) (fun s _ => by
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [(hb s).1, (hb s).2])
    simpa using this
  have hder : ∀ t, HasDerivAt Φ 0 t := by
    intro t
    rw [hasDerivAt_iff_isLittleO]
    -- part A
    have hA : (fun y => L (E y) - L (E t) - (E y - E t) * h (E t)) =o[𝓝 t]
        (fun y => y - t) := by
      have h1 := (hasDerivAt_iff_isLittleO.mp (hL (E t))).comp_tendsto (hEc.tendsto t)
      have h2 : (fun y => E y - E t) =O[𝓝 t] (fun y => y - t) :=
        IsBigO.of_bound 1 (Eventually.of_forall fun y => by
          simpa [Real.norm_eq_abs] using hlip t y)
      have := h1.trans_isBigO h2
      refine this.congr_left (fun y => ?_)
      simp [smul_eq_mul]
    -- part B
    have hB : (fun y => ∫ s in t..y, g s * (h (E t) - h (E s))) =o[𝓝 t]
        (fun y => y - t) := by
      rw [isLittleO_iff]
      intro c hc
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hhE.continuousAt c hc
      filter_upwards [Metric.ball_mem_nhds t hδ] with y hy
      have hy' : |y - t| < δ := by simpa [Real.dist_eq] using hy
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := y) (C := c)
        (f := fun s => g s * (h (E t) - h (E s))) (fun s hs => by
          have hs' : |s - t| ≤ |y - t| := abs_sub_left_of_mem_uIcc (uIoc_subset_uIcc hs)
          have hd := hδc (x := s) (by rw [Real.dist_eq]; linarith)
          rw [Real.dist_eq] at hd
          rw [Real.norm_eq_abs, abs_mul]
          have hg0 := (hb s).1
          have hg1 := (hb s).2
          rw [abs_of_nonneg hg0, abs_sub_comm]
          calc g s * |h (E s) - h (E t)| ≤ 1 * c := by
                apply mul_le_mul hg1 hd.le (abs_nonneg _) zero_le_one
            _ = c := one_mul c)
      simpa [Real.norm_eq_abs, mul_comm] using this
    refine (hA.add hB).congr_left (fun y => ?_)
    have e1 : (∫ s in t0..y, g s * h (E s)) - ∫ s in t0..t, g s * h (E s) =
        ∫ s in t..y, g s * h (E s) :=
      intervalIntegral.integral_interval_sub_left (hii2 _ _) (hii2 _ _)
    have e2 : ∫ s in t..y, g s * (h (E t) - h (E s)) =
        (∫ s in t..y, g s) * h (E t) - ∫ s in t..y, g s * h (E s) := by
      rw [← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_sub
        ((hii _ _).mul_const _) (hii2 _ _)]
      congr 1; ext s; ring
    rw [e2, ← hEsub t y]
    simp only [hΦ, smul_zero, sub_zero]
    linarith [e1]
  have hconst := is_const_of_deriv_eq_zero (fun x => (hder x).differentiableAt)
    (fun x => (hder x).deriv)
  intro t
  have := hconst t t0
  simp only [hΦ, hE, intervalIntegral.integral_same, sub_zero] at this
  linarith

/-- Gronwall uniqueness for the integral-form logistic equation. -/
lemma unique_path (γ : ℝ) (hγ : 0 ≤ γ) (g : ℝ → ℝ) (hb : ∀ s, g s ∈ Icc (0:ℝ) 1)
    (hii : ∀ a c, IntervalIntegrable g volume a c) (t0 c0 : ℝ) (p q : ℝ → ℝ)
    (hp : ContinuousOn p (Ici t0)) (hq : Continuous q)
    (hp1 : ∀ t, t0 ≤ t → p t ∈ Icc (0:ℝ) 1) (hq1 : ∀ t, q t ∈ Icc (0:ℝ) 1)
    (hpe : ∀ t, t0 ≤ t → p t = c0 + ∫ s in t0..t, γ * g s * p s * (1 - p s))
    (hqe : ∀ t, t0 ≤ t → q t = c0 + ∫ s in t0..t, γ * g s * q s * (1 - q s)) :
    ∀ t, t0 ≤ t → p t = q t := by
  set pt : ℝ → ℝ := fun s => p (max s t0) with hpt
  have hptc : Continuous pt :=
    hp.comp_continuous (continuous_id.max continuous_const) (fun s => show t0 ≤ max s t0 from le_max_right _ _)
  set w : ℝ → ℝ := fun s => |pt s - q s| with hw
  have hwc : Continuous w := (hptc.sub hq).abs
  set W : ℝ → ℝ := fun x => ∫ s in t0..x, w s with hW
  have hpt_eq : ∀ s, t0 ≤ s → pt s = p s := fun s hs => by simp [hpt, max_eq_left hs]
  have claim1 : ∀ x, t0 ≤ x → |p x - q x| ≤ γ * W x := by
    intro x hx
    have hpo : ContinuousOn p (uIcc t0 x) := hp.mono (by
      rw [uIcc_of_le hx]; exact Icc_subset_Ici_self)
    have i1 : IntervalIntegrable (fun s => γ * g s * p s * (1 - p s)) volume t0 x :=
      (((hii t0 x).const_mul γ).mul_continuousOn hpo).mul_continuousOn
        (continuousOn_const.sub hpo)
    have i2 : IntervalIntegrable (fun s => γ * g s * q s * (1 - q s)) volume t0 x :=
      (((hii t0 x).const_mul γ).mul_continuousOn hq.continuousOn).mul_continuousOn
        (continuousOn_const.sub hq.continuousOn)
    have hdiff : p x - q x = ∫ s in t0..x,
        (γ * g s * p s * (1 - p s) - γ * g s * q s * (1 - q s)) := by
      rw [intervalIntegral.integral_sub i1 i2, hpe x hx, hqe x hx]; ring
    rw [hdiff]
    calc |∫ s in t0..x, (γ * g s * p s * (1 - p s) - γ * g s * q s * (1 - q s))|
        ≤ ∫ s in t0..x, ‖γ * g s * p s * (1 - p s) - γ * g s * q s * (1 - q s)‖ :=
          by rw [← Real.norm_eq_abs]; exact intervalIntegral.norm_integral_le_integral_norm hx
      _ ≤ ∫ s in t0..x, γ * w s := by
          apply intervalIntegral.integral_mono_on hx
          · exact (i1.sub i2).norm
          · exact (hwc.const_mul γ).intervalIntegrable _ _
          · intro s hs
            have hs0 : t0 ≤ s := hs.1
            have hpq : w s = |p s - q s| := by simp [hw, hpt_eq s hs0]
            rw [hpq]
            have hps := hp1 s hs0
            have hqs := hq1 s
            have h0 := (hb s).1
            have h2 := (hb s).2
            have e : γ * g s * p s * (1 - p s) - γ * g s * q s * (1 - q s) =
                γ * g s * (p s - q s) * (1 - p s - q s) := by ring
            have h1 : |1 - p s - q s| ≤ 1 := by
              rw [abs_le]; constructor <;> linarith [hps.1, hps.2, hqs.1, hqs.2]
            rw [Real.norm_eq_abs, e, abs_mul, abs_mul, abs_mul, abs_of_nonneg hγ,
              abs_of_nonneg h0]
            calc γ * g s * |p s - q s| * |1 - p s - q s|
                ≤ γ * g s * |p s - q s| * 1 :=
                  mul_le_mul_of_nonneg_left h1 (mul_nonneg (mul_nonneg hγ h0) (abs_nonneg _))
              _ = γ * |p s - q s| * g s := by ring
              _ ≤ γ * |p s - q s| * 1 :=
                  mul_le_mul_of_nonneg_left h2 (mul_nonneg hγ (abs_nonneg _))
              _ = γ * |p s - q s| := by ring
      _ = γ * W x := by rw [intervalIntegral.integral_const_mul]
  intro t ht
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := W) (f' := w) (δ := 0) (K := γ)
    (ε := 0) (a := t0) (b := t)
    ((intervalIntegral.continuous_primitive (fun a c => hwc.intervalIntegrable a c) t0).continuousOn)
    (fun x _ => (hwc.integral_hasStrictDerivAt t0 x).hasDerivAt.hasDerivWithinAt)
    (by simp [hW])
    (fun x hx => by
      have hx0 : t0 ≤ x := hx.1
      have : ‖w x‖ = |p x - q x| := by
        simp [hw, hpt_eq x hx0]
      rw [this, add_zero]
      exact (claim1 x hx0).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hγ))
    t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0_δ0] at hg
  have hW0 : |W t| ≤ 0 := by simpa using hg
  have := claim1 t ht
  have : |p t - q t| ≤ 0 := by
    calc |p t - q t| ≤ γ * W t := this
      _ ≤ γ * |W t| := mul_le_mul_of_nonneg_left (le_abs_self _) hγ
      _ ≤ γ * 0 := mul_le_mul_of_nonneg_left hW0 hγ
      _ = 0 := by ring
  have := abs_nonpos_iff.mp this
  linarith

end RotContLemma1

open RotationContagion.Rotation RotContLemma1 in
theorem solution (P : Params) (hP : P.Standing) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r)
    (ω : Fin 2) (t0 : ℝ) (ht0 : 0 ≤ t0) :
    IsPrevalencePath P r ω t0 (fun t => loss P (∫ s in t0..t, r ω s)) ∧
      ∀ p : ℝ → ℝ, IsPrevalencePath P r ω t0 p →
        (∀ t : ℝ, t0 ≤ t → p t = loss P (∫ s in t0..t, r ω s)) ∧
          p (t0 + P.R) = loss P (exposure P r ω t0) := by
  obtain ⟨hode0, hode⟩ := loss_ode P hP
  obtain ⟨hγ, hK, hR⟩ := hP
  have hgm : Measurable (r ω) := hr.1 ω
  have hb : ∀ s, r ω s ∈ Set.Icc (0:ℝ) 1 := fun s => (hr.2 s).1 ω
  have hii : ∀ a c, IntervalIntegrable (r ω) MeasureTheory.volume a c := ii_of_bdd _ hgm hb
  have hEc : Continuous (fun t => ∫ s in t0..t, r ω s) :=
    intervalIntegral.continuous_primitive hii t0
  have hLc : Continuous (loss P) :=
    continuous_iff_continuousAt.2 fun x => (hode x).continuousAt
  have hcont_h : Continuous (fun x => P.γ * loss P x * (1 - loss P x)) := by fun_prop
  have key := key_deriv (loss P) (fun x => P.γ * loss P x * (1 - loss P x)) hode hcont_h
    (r ω) hb hii t0
  have hqc : Continuous (fun t => loss P (∫ s in t0..t, r ω s)) := hLc.comp hEc
  have qeq : ∀ t, t0 ≤ t → loss P (∫ s in t0..t, r ω s) = 1 / P.K +
      ∫ s in t0..t, P.γ * r ω s * loss P (∫ u in t0..s, r ω u) *
        (1 - loss P (∫ u in t0..s, r ω u)) := by
    intro t _
    rw [key t, hode0]
    congr 1
    apply intervalIntegral.integral_congr
    intro s _
    simp only
    ring
  have hq : IsPrevalencePath P r ω t0 (fun t => loss P (∫ s in t0..t, r ω s)) :=
    ⟨hqc.continuousOn, fun t _ => loss_mem P _, qeq⟩
  refine ⟨hq, fun p hp => ?_⟩
  have huniq := unique_path P.γ hγ.le (r ω) hb hii t0 (1 / P.K) p
    (fun t => loss P (∫ s in t0..t, r ω s)) hp.1 hqc hp.2.1 (fun t => loss_mem P _) hp.2.2 qeq
  refine ⟨huniq, ?_⟩
  exact huniq (t0 + P.R) (by linarith)
