-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.joint_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:38:01.241331+00:00
-- url     : https://prove2.me/submissions/09a979ef-3457-4eeb-9daf-2bc2cbed5c25

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem aux_joi_int {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (h p y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x : ℝ => max (y - x) 0) μ :=
    ((integrable_const y).sub hint).pos_part
  have h2 : Integrable (fun x : ℝ => max (x - y) 0) μ :=
    (hint.sub (integrable_const y)).pos_part
  exact (h1.const_mul h).add (h2.const_mul p)

theorem aux_joi_conv {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) {h p : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  simp only [smul_eq_mul, newsvendorCost]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_joi_int hint h p x).const_mul a) ((aux_joi_int hint h p y).const_mul b)]
  refine integral_mono (aux_joi_int hint h p _)
    (((aux_joi_int hint h p x).const_mul a).add ((aux_joi_int hint h p y).const_mul b)) ?_
  intro z
  have e1 : a * x + b * y - z = a * (x - z) + b * (y - z) := by
    have : b = 1 - a := by linarith
    subst this; ring
  have e2 : z - (a * x + b * y) = a * (z - x) + b * (z - y) := by
    have : b = 1 - a := by linarith
    subst this; ring
  have m1 : max (a * x + b * y - z) 0 ≤ a * max (x - z) 0 + b * max (y - z) 0 := by
    rw [e1]
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (x - z) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (y - z) 0) hb
      linarith
    · have := mul_nonneg ha (le_max_right (x - z) 0)
      have := mul_nonneg hb (le_max_right (y - z) 0)
      linarith
  have m2 : max (z - (a * x + b * y)) 0 ≤ a * max (z - x) 0 + b * max (z - y) 0 := by
    rw [e2]
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (z - x) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (z - y) 0) hb
      linarith
    · have := mul_nonneg ha (le_max_right (z - x) 0)
      have := mul_nonneg hb (le_max_right (z - y) 0)
      linarith
  have := mul_le_mul_of_nonneg_left m1 hh
  have := mul_le_mul_of_nonneg_left m2 hp
  show h * max (a * x + b * y - z) 0 + p * max (z - (a * x + b * y)) 0 ≤
    a * (h * max (x - z) 0 + p * max (z - x) 0) + b * (h * max (y - z) 0 + p * max (z - y) 0)
  nlinarith

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic
open MeasureTheory Filter Topology

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q r : ℝ) (hQ : 0 < Q) :
    (∀ Q' r' : ℝ, 0 < Q' → qrCost (newsvendorCost μ h p) lam K Q r ≤ qrCost (newsvendorCost μ h p) lam K Q' r') ↔
      (qrCost (newsvendorCost μ h p) lam K Q r = newsvendorCost μ h p r ∧ newsvendorCost μ h p r = newsvendorCost μ h p (r + Q)) := by
  have := hM.isProb
  set G := newsvendorCost μ h p with hGdef
  have hconv : ConvexOn ℝ Set.univ G := aux_joi_conv hM.integrable hM.h_pos.le hM.p_pos.le
  have hcont : Continuous G := by
    rw [← continuousOn_univ]
    exact hconv.continuousOn isOpen_univ
  set F : ℝ → ℝ := fun u => ∫ y in (0:ℝ)..u, G y with hFdef
  have hF : ∀ b, HasDerivAt F (G b) b := fun b => (hcont.integral_hasStrictDerivAt 0 b).hasDerivAt
  have hint : ∀ a b : ℝ, ∫ y in a..b, G y = F b - F a := by
    intro a b
    rw [hFdef]
    exact (intervalIntegral.integral_interval_sub_left (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hq : ∀ Q' r', qrCost G lam K Q' r' = (lam * K + (F (r' + Q') - F r')) / Q' := by
    intro Q' r'
    simp only [qrCost, hint]
  constructor
  · intro hmin
    -- r-direction
    have hr : G (r + Q) = G r := by
      have hd : HasDerivAt (fun r' => (lam * K + (F (r' + Q) - F r')) / Q)
          ((0 + (G (r + Q) * 1 - G r)) / Q) r := by
        refine HasDerivAt.div_const ?_ Q
        refine (hasDerivAt_const r (lam * K)).add ?_
        refine HasDerivAt.sub ?_ (hF r)
        exact (hF (r + Q)).comp r ((hasDerivAt_id r).add_const Q)
      have hlm : IsLocalMin (fun r' => (lam * K + (F (r' + Q) - F r')) / Q) r := by
        refine Filter.Eventually.of_forall (fun r' => ?_)
        have := hmin Q r' hQ
        simp only [hq] at this
        exact this
      have := hlm.hasDerivAt_eq_zero hd
      rw [div_eq_zero_iff] at this
      rcases this with h0 | h0
      · linarith
      · exact absurd h0 hQ.ne'
    -- Q-direction
    have hc : qrCost G lam K Q r = G (r + Q) := by
      have hd : HasDerivAt (fun Q' => (lam * K + (F (r + Q') - F r)) / Q')
          (((0 + (G (r + Q) * 1 - 0)) * Q - (lam * K + (F (r + Q) - F r)) * 1) / Q ^ 2) Q := by
        refine HasDerivAt.div ?_ (hasDerivAt_id Q) hQ.ne'
        refine (hasDerivAt_const Q (lam * K)).add ?_
        refine HasDerivAt.sub ?_ (hasDerivAt_const Q (F r))
        exact (hF (r + Q)).comp Q ((hasDerivAt_id Q).const_add r)
      have hlm : IsLocalMin (fun Q' => (lam * K + (F (r + Q') - F r)) / Q') Q := by
        filter_upwards [Ioi_mem_nhds hQ] with Q' hQ'
        have := hmin Q' r hQ'
        simp only [hq] at this
        exact this
      have := hlm.hasDerivAt_eq_zero hd
      rw [div_eq_zero_iff] at this
      rcases this with h0 | h0
      · rw [hq, div_eq_iff hQ.ne']
        linarith
      · exact absurd h0 (pow_ne_zero 2 hQ.ne')
    exact ⟨hc.trans hr, hr.symm⟩
  · rintro ⟨hc, hr⟩ Q' r' hQ'
    set c := G r with hcdef
    -- shape of G
    have hin : ∀ y ∈ Set.Icc r (r + Q), G y ≤ c := by
      intro y hy
      have := hconv.le_on_segment (Set.mem_univ r) (Set.mem_univ (r + Q))
        (by rw [segment_eq_Icc (by linarith)]; exact hy)
      rw [← hr, max_self] at this
      exact this
    have hout : ∀ y, y ∉ Set.Icc r (r + Q) → c ≤ G y := by
      intro y hy
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hy | hy
      · have := hconv.slope_mono_adjacent (Set.mem_univ y) (Set.mem_univ (r + Q)) hy
          (by linarith : r < r + Q)
        rw [← hr, sub_self, zero_div] at this
        have hpos : 0 < r - y := by linarith
        rw [div_nonpos_iff] at this
        rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
        · linarith
        · linarith
      · have := hconv.slope_mono_adjacent (Set.mem_univ r) (Set.mem_univ y)
          (by linarith : r < r + Q) hy
        rw [← hr, sub_self, zero_div] at this
        have hpos : 0 < y - (r + Q) := by linarith
        rw [le_div_iff₀ hpos, zero_mul] at this
        rw [hr]; linarith
    set φ : ℝ → ℝ := fun y => max (c - G y) 0 with hφdef
    have hφcont : Continuous φ := (continuous_const.sub hcont).max continuous_const
    have hφzero : ∀ y, y ∉ Set.Icc r (r + Q) → φ y = 0 := by
      intro y hy
      simp only [hφdef]
      exact max_eq_right (by linarith [hout y hy])
    have hφint : Integrable φ := by
      refine hφcont.integrable_of_hasCompactSupport ?_
      refine HasCompactSupport.intro (isCompact_Icc (a := r) (b := r + Q)) ?_
      exact hφzero
    have hφnn : ∀ y, 0 ≤ φ y := fun y => le_max_right _ _
    -- total mass of φ
    have hmass : ∫ y, φ y = lam * K := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφzero, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : r ≤ r + Q)]
      have : ∫ y in r..r + Q, φ y = ∫ y in r..r + Q, (c - G y) := by
        refine intervalIntegral.integral_congr (fun y hy => ?_)
        rw [Set.uIcc_of_le (by linarith : r ≤ r + Q)] at hy
        simp only [hφdef]
        exact max_eq_left (by linarith [hin y hy])
      rw [this, intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_eq_mul]
      have hc' := hc
      rw [qrCost, div_eq_iff hQ.ne'] at hc'
      linarith
    -- the key inequality
    have hkey : ∫ y in r'..r' + Q', (c - G y) ≤ lam * K := by
      calc ∫ y in r'..r' + Q', (c - G y) ≤ ∫ y in r'..r' + Q', φ y := by
            refine intervalIntegral.integral_mono_on (by linarith)
              (intervalIntegrable_const.sub (hcont.intervalIntegrable _ _))
              (hφcont.intervalIntegrable _ _) (fun y _ => le_max_left _ _)
        _ = ∫ y in Set.Ioc r' (r' + Q'), φ y := intervalIntegral.integral_of_le (by linarith)
        _ ≤ ∫ y, φ y := setIntegral_le_integral hφint (Filter.Eventually.of_forall hφnn)
        _ = lam * K := hmass
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hcont.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul] at hkey
    rw [hc]
    show c ≤ (lam * K + ∫ y in r'..r' + Q', G y) / Q'
    rw [le_div_iff₀ hQ']
    linarith
