-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.optQty_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:43:36.755618+00:00
-- url     : https://prove2.me/submissions/0a71b4db-4149-423b-a51f-fb774af8df78

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

open Set

lemma aux_oqi_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ] (h p : ℝ)
    (hi : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x => y - x) μ := (integrable_const y).sub hi
  have h2 : Integrable (fun x => x - y) μ := hi.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_oqi_pt (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p) (x y z a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    h * max (a * y + b * z - x) 0 + p * max (x - (a * y + b * z)) 0 ≤
      a * (h * max (y - x) 0 + p * max (x - y) 0) + b * (h * max (z - x) 0 + p * max (x - z) 0) := by
  have e1 : max (a * y + b * z - x) 0 ≤ a * max (y - x) 0 + b * max (z - x) 0 := by
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (z - x) 0) hb
      have hx : a * y + b * z - x = a * (y - x) + b * (z - x) := by
        have : x = (a + b) * x := by rw [hab]; ring
        linarith
      linarith
    · have := mul_nonneg ha (le_max_right (y - x) 0)
      have := mul_nonneg hb (le_max_right (z - x) 0)
      linarith
  have e2 : max (x - (a * y + b * z)) 0 ≤ a * max (x - y) 0 + b * max (x - z) 0 := by
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) ha
      have := mul_le_mul_of_nonneg_left (le_max_left (x - z) 0) hb
      have hx : x - (a * y + b * z) = a * (x - y) + b * (x - z) := by
        have : x = (a + b) * x := by rw [hab]; ring
        linarith
      linarith
    · have := mul_nonneg ha (le_max_right (x - y) 0)
      have := mul_nonneg hb (le_max_right (x - z) 0)
      linarith
  have f1 := mul_le_mul_of_nonneg_left e1 hh
  have f2 := mul_le_mul_of_nonneg_left e2 hp
  linarith

lemma aux_oqi_convex {μ : Measure ℝ} [IsProbabilityMeasure μ] (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hi : Integrable (fun x : ℝ => x) μ) : ConvexOn ℝ univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ a b ha hb hab
  simp only [smul_eq_mul, newsvendorCost]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · refine integral_mono (aux_oqi_integrable h p hi _) ?_ ?_
    · exact ((aux_oqi_integrable h p hi y).const_mul a).add
        ((aux_oqi_integrable h p hi z).const_mul b)
    · intro x
      exact aux_oqi_pt h p hh hp x y z a b ha hb hab
  · exact (aux_oqi_integrable h p hi y).const_mul a
  · exact (aux_oqi_integrable h p hi z).const_mul b

lemma aux_oqi_lb1 {μ : Measure ℝ} [IsProbabilityMeasure μ] (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hi : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    h * (y - ∫ x, x ∂μ) ≤ newsvendorCost μ h p y := by
  have hI : Integrable (fun x : ℝ => h * (y - x)) μ :=
    ((integrable_const y).sub hi).const_mul h
  have e : ∫ x, h * (y - x) ∂μ = h * (y - ∫ x, x ∂μ) := by
    rw [integral_const_mul, integral_sub (integrable_const y) hi]
    simp
  rw [← e]
  refine integral_mono hI (aux_oqi_integrable h p hi y) ?_
  intro x
  have := mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) hh
  have := mul_nonneg hp (le_max_right (x - y) 0)
  simp only
  linarith

lemma aux_oqi_lb2 {μ : Measure ℝ} [IsProbabilityMeasure μ] (h p : ℝ) (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hi : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    p * ((∫ x, x ∂μ) - y) ≤ newsvendorCost μ h p y := by
  have hI : Integrable (fun x : ℝ => p * (x - y)) μ :=
    (hi.sub (integrable_const y)).const_mul p
  have e : ∫ x, p * (x - y) ∂μ = p * ((∫ x, x ∂μ) - y) := by
    rw [integral_const_mul, integral_sub hi (integrable_const y)]
    simp
  rw [← e]
  refine integral_mono hI (aux_oqi_integrable h p hi y) ?_
  intro x
  have := mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) hp
  have := mul_nonneg hh (le_max_right (y - x) 0)
  simp only
  linarith

/-- primitive identity -/
lemma aux_oqi_prim {G : ℝ → ℝ} (hGc : Continuous G) (s t : ℝ) :
    ∫ y in s..t, G y = (∫ y in (0:ℝ)..t, G y) - ∫ y in (0:ℝ)..s, G y :=
  (intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable _ _)
    (hGc.intervalIntegrable _ _)).symm

lemma aux_oqi_exists {G : ℝ → ℝ} (hGc : Continuous G) (h p m : ℝ) (hh : 0 < h) (hp : 0 < p)
    (hG1 : ∀ y, h * (y - m) ≤ G y) (hG2 : ∀ y, p * (m - y) ≤ G y) (Q : ℝ) (hQ : 0 < Q) :
    ∃ r, ∀ r', ∫ y in r..r + Q, G y ≤ ∫ y in r'..r' + Q, G y := by
  set Φ : ℝ → ℝ := fun u => ∫ y in (0:ℝ)..u, G y with hΦdef
  have hΦ : ∀ u, HasDerivAt Φ (G u) u := fun u => (hGc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hΦc : Continuous Φ := continuous_iff_continuousAt.2 fun u => (hΦ u).continuousAt
  have hφc : Continuous (fun r => ∫ y in r..r + Q, G y) := by
    have : (fun r => ∫ y in r..r + Q, G y) = fun r => Φ (r + Q) - Φ r := by
      funext r; exact aux_oqi_prim hGc r (r + Q)
    rw [this]
    exact (hΦc.comp (continuous_id.add continuous_const)).sub hΦc
  set φ0 := ∫ y in (0:ℝ)..0 + Q, G y
  refine hφc.exists_forall_le' 0 ?_
  rw [cocompact_eq_atBot_atTop, eventually_sup]
  have hQh : 0 < Q * h := mul_pos hQ hh
  have hQp : 0 < Q * p := mul_pos hQ hp
  constructor
  · rw [eventually_atBot]
    refine ⟨m - Q - φ0 / (Q * p), fun r hr => ?_⟩
    have hb : ∫ y in r..r + Q, Q⁻¹ * (Q * p * (m - r - Q)) ≤ ∫ y in r..r + Q, G y := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hGc.intervalIntegrable _ _) ?_
      intro y hy
      have h1 := hG2 y
      have h2 : p * (m - r - Q) ≤ p * (m - y) := by
        apply mul_le_mul_of_nonneg_left _ hp.le; linarith [hy.2]
      have : Q⁻¹ * (Q * p * (m - r - Q)) = p * (m - r - Q) := by field_simp
      linarith
    have hc : ∫ y in r..r + Q, Q⁻¹ * (Q * p * (m - r - Q)) = Q * p * (m - r - Q) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
    rw [hc] at hb
    have : φ0 ≤ Q * p * (m - r - Q) := by
      have e : Q * p * (φ0 / (Q * p)) = φ0 := by field_simp
      have : φ0 / (Q * p) ≤ m - r - Q := by linarith
      have := mul_le_mul_of_nonneg_left this hQp.le
      linarith
    linarith
  · rw [eventually_atTop]
    refine ⟨m + φ0 / (Q * h), fun r hr => ?_⟩
    have hb : ∫ y in r..r + Q, Q⁻¹ * (Q * h * (r - m)) ≤ ∫ y in r..r + Q, G y := by
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hGc.intervalIntegrable _ _) ?_
      intro y hy
      have h1 := hG1 y
      have h2 : h * (r - m) ≤ h * (y - m) := by
        apply mul_le_mul_of_nonneg_left _ hh.le; linarith [hy.1]
      have : Q⁻¹ * (Q * h * (r - m)) = h * (r - m) := by field_simp
      linarith
    have hc : ∫ y in r..r + Q, Q⁻¹ * (Q * h * (r - m)) = Q * h * (r - m) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]; field_simp; ring
    rw [hc] at hb
    have : φ0 ≤ Q * h * (r - m) := by
      have e : Q * h * (φ0 / (Q * h)) = φ0 := by field_simp
      have : φ0 / (Q * h) ≤ r - m := by linarith
      have := mul_le_mul_of_nonneg_left this hQh.le
      linarith
    linarith

lemma aux_oqi_foc {G : ℝ → ℝ} (hGc : Continuous G) (lam K q r : ℝ) (hq : 0 < q)
    (hr : IsOptReorder G lam K q r) : G (r + q) = G r := by
  set Φ : ℝ → ℝ := fun u => ∫ y in (0:ℝ)..u, G y with hΦdef
  have hΦ : ∀ u, HasDerivAt Φ (G u) u := fun u => (hGc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have key : (fun s => qrCost G lam K q s) = fun s => (lam * K + (Φ (s + q) - Φ s)) / q := by
    funext s
    simp only [qrCost]
    rw [aux_oqi_prim hGc s (s + q)]
  have hmin : IsLocalMin (fun s => qrCost G lam K q s) r :=
    Filter.Eventually.of_forall fun s => hr s
  rw [key] at hmin
  have hd : HasDerivAt (fun s => (lam * K + (Φ (s + q) - Φ s)) / q)
      ((G (r + q) - G r) / q) r := by
    have h1 : HasDerivAt (fun s => Φ (s + q)) (G (r + q)) r :=
      HasDerivAt.comp_add_const r q (hΦ (r + q))
    exact ((h1.sub (hΦ r)).const_add (lam * K)).div_const q
  have := hmin.hasDerivAt_eq_zero hd
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · exact absurd h hq.ne'

lemma aux_oqi_levels {G : ℝ → ℝ} (hc : ConvexOn ℝ univ G) (a b : ℝ) (hab : a < b)
    (hG : G b = G a) :
    (∀ y ∈ Icc a b, G y ≤ G a) ∧ (∀ y, y ≤ a → G a ≤ G y) ∧ (∀ y, b ≤ y → G a ≤ G y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    have := hc.le_on_segment (mem_univ a) (mem_univ b) (by rw [segment_eq_Icc hab.le]; exact hy)
    rw [hG, max_self] at this
    exact this
  · intro y hy
    have := hc.le_left_of_right_le'' (mem_univ y) (mem_univ b) hy hab (by rw [hG])
    exact this
  · intro y hy
    have := hc.le_right_of_left_le'' (mem_univ a) (mem_univ y) hab hy (by rw [hG])
    rw [← hG]; exact this

lemma aux_oqi_sub {G : ℝ → ℝ} (hGc : Continuous G) (a b H : ℝ) (hab : a ≤ b)
    (hle : ∀ y ∈ Icc a b, G y ≤ H) (hge1 : ∀ y, y ≤ a → H ≤ G y) (hge2 : ∀ y, b ≤ y → H ≤ G y)
    (s t : ℝ) (hst : s ≤ t) :
    (∫ y in a..b, G y) - (b - a) * H ≤ (∫ y in s..t, G y) - (t - s) * H := by
  set g : ℝ → ℝ := fun y => G y - H with hgdef
  have hgc : Continuous g := hGc.sub continuous_const
  have hI : ∀ u v : ℝ, ∫ y in u..v, g y = (∫ y in u..v, G y) - (v - u) * H := by
    intro u v
    simp only [hgdef]
    rw [intervalIntegral.integral_sub (hGc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
  rw [← hI, ← hI]
  have hii : ∀ u v : ℝ, IntervalIntegrable g volume u v := fun u v => hgc.intervalIntegrable _ _
  -- nonneg/nonpos facts
  have hneg : ∫ y in a..b, g y ≤ 0 := by
    have : 0 ≤ ∫ y in a..b, -g y := by
      refine intervalIntegral.integral_nonneg hab ?_
      intro y hy; simp only [hgdef]; linarith [hle y hy]
    rw [intervalIntegral.integral_neg] at this
    linarith
  -- ∫_s^a g ≥ 0 when s ≤ b
  have hleft : s ≤ b → 0 ≤ ∫ y in s..a, g y := by
    intro hsb
    rcases le_total s a with hsa | has
    · refine intervalIntegral.integral_nonneg hsa ?_
      intro y hy; simp only [hgdef]; linarith [hge1 y hy.2]
    · rw [intervalIntegral.integral_symm]
      have : 0 ≤ ∫ y in a..s, -g y := by
        refine intervalIntegral.integral_nonneg has ?_
        intro y hy; simp only [hgdef]; linarith [hle y ⟨hy.1, hy.2.trans hsb⟩]
      rw [intervalIntegral.integral_neg] at this
      linarith
  have hright : a ≤ t → 0 ≤ ∫ y in b..t, g y := by
    intro hat
    rcases le_total b t with hbt | htb
    · refine intervalIntegral.integral_nonneg hbt ?_
      intro y hy; simp only [hgdef]; linarith [hge2 y hy.1]
    · rw [intervalIntegral.integral_symm]
      have : 0 ≤ ∫ y in t..b, -g y := by
        refine intervalIntegral.integral_nonneg htb ?_
        intro y hy; simp only [hgdef]; linarith [hle y ⟨hat.trans hy.1, hy.2⟩]
      rw [intervalIntegral.integral_neg] at this
      linarith
  by_cases hsb : s ≤ b
  · by_cases hat : a ≤ t
    · have e1 := intervalIntegral.integral_add_adjacent_intervals (hii s a) (hii a b)
      have e2 := intervalIntegral.integral_add_adjacent_intervals (hii s b) (hii b t)
      have := hleft hsb
      have := hright hat
      linarith
    · rw [not_le] at hat
      have : 0 ≤ ∫ y in s..t, g y := by
        refine intervalIntegral.integral_nonneg hst ?_
        intro y hy; simp only [hgdef]; linarith [hge1 y (hy.2.trans hat.le)]
      linarith
  · rw [not_le] at hsb
    have : 0 ≤ ∫ y in s..t, g y := by
      refine intervalIntegral.integral_nonneg hst ?_
      intro y hy; simp only [hgdef]; linarith [hge2 y (hsb.le.trans hy.1)]
    linarith

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    IsOptQty (newsvendorCost μ h p) lam K Q ↔ hFun (newsvendorCost μ h p) lam K Q = optCost (newsvendorCost μ h p) lam K Q := by
  have := hM.isProb
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hi := hM.integrable
  set G := newsvendorCost μ h p with hGdef
  have hGconv : ConvexOn ℝ Set.univ G := aux_oqi_convex h p hh.le hp.le hi
  have hGc : Continuous G := continuousOn_univ.1 (hGconv.continuousOn isOpen_univ)
  have hopt : ∀ q, 0 < q → IsOptReorder G lam K q (reorderPt G lam K q) := by
    intro q hq
    have hex : ∃ r, IsOptReorder G lam K q r := by
      obtain ⟨r, hr⟩ := aux_oqi_exists hGc h p (∫ x, x ∂μ) hh hp
        (aux_oqi_lb1 h p hh.le hp.le hi) (aux_oqi_lb2 h p hh.le hp.le hi) q hq
      refine ⟨r, fun r' => ?_⟩
      simp only [qrCost]
      gcongr
      exact hr r'
    unfold reorderPt
    rw [dif_pos hex]
    exact hex.choose_spec
  set r := reorderPt G lam K Q with hrdef
  have hr := hopt Q hQ
  have hH : hFun G lam K Q = G r := by simp only [hFun, if_pos hQ, hrdef]
  have hrq : G (r + Q) = G r := aux_oqi_foc hGc lam K Q r hQ hr
  have hC : optCost G lam K Q = (lam * K + ∫ y in r..r + Q, G y) / Q := rfl
  rw [hH, hC]
  constructor
  · rintro ⟨_, hmin⟩
    set ψ : ℝ → ℝ := fun q => (lam * K + ∫ y in r..r + q, G y) / q with hψdef
    have hloc : IsLocalMin ψ Q := by
      filter_upwards [Ioi_mem_nhds hQ] with q hq
      have h1 := hmin q hq
      have h2 := hopt q hq r
      simp only [optCost, qrCost] at h1 h2
      simp only [hψdef]
      exact h1.trans h2
    have hd0 : HasDerivAt (fun q => ∫ y in r..q, G y) (G (r + Q)) (r + Q) :=
      (hGc.integral_hasStrictDerivAt r (r + Q)).hasDerivAt
    have hd1 : HasDerivAt (fun q => ∫ y in r..r + q, G y) (G (r + Q)) Q :=
      HasDerivAt.comp_const_add r Q hd0
    have hd : HasDerivAt ψ
        ((G (r + Q) * Q - (lam * K + ∫ y in r..r + Q, G y) * 1) / Q ^ 2) Q :=
      (hd1.const_add (lam * K)).div (hasDerivAt_id Q) hQ.ne'
    have := hloc.hasDerivAt_eq_zero hd
    rw [div_eq_zero_iff] at this
    rcases this with h0 | h0
    · rw [← hrq, eq_div_iff hQ.ne']
      linarith
    · exact absurd h0 (pow_ne_zero 2 hQ.ne')
  · intro heq
    refine ⟨hQ, fun Q' hQ' => ?_⟩
    rw [hC, ← heq]
    obtain ⟨hle, hge1, hge2⟩ := aux_oqi_levels hGconv r (r + Q) (by linarith) hrq
    set r' := reorderPt G lam K Q'
    have hs := aux_oqi_sub hGc r (r + Q) (G r) (by linarith) hle hge1 hge2 r' (r' + Q')
      (by linarith)
    have hF : (∫ y in r..r + Q, G y) = Q * G r - lam * K := by
      rw [eq_div_iff hQ.ne'] at heq
      linarith
    show G r ≤ (lam * K + ∫ y in r'..r' + Q', G y) / Q'
    rw [le_div_iff₀ hQ']
    have : r + Q - r = Q := by ring
    have : r' + Q' - r' = Q' := by ring
    nlinarith
