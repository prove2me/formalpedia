-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.eoqQty_le_optQty
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:53:35.98673+00:00
-- url     : https://prove2.me/submissions/717f0015-a714-4d67-af4d-8f7d7a75e23b

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem aux_eoq_int {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hM.isProb
  exact (((integrable_const y).sub hM.integrable).pos_part.const_mul h).add
    ((hM.integrable.sub (integrable_const y)).pos_part.const_mul p)

theorem aux_eoq_up {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {x y : ℝ}
    (hxy : x ≤ y) : newsvendorCost μ h p y ≤ newsvendorCost μ h p x + h * (y - x) := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ ≤
      ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0 + h * (y - x)) ∂μ :=
    integral_mono (aux_eoq_int hM y) ((aux_eoq_int hM x).add (integrable_const (h * (y - x))))
    (fun ω => by
      have h1 : max (y - ω) 0 ≤ max (x - ω) 0 + (y - x) :=
        max_le (by linarith [le_max_left (x - ω) 0]) (by linarith [le_max_right (x - ω) 0])
      have h2 : max (ω - y) 0 ≤ max (ω - x) 0 := max_le_max (by linarith) le_rfl
      have := mul_le_mul_of_nonneg_left h1 hM.h_pos.le
      have := mul_le_mul_of_nonneg_left h2 hM.p_pos.le
      simp only [Pi.add_apply]
      nlinarith)
  rw [integral_add (aux_eoq_int hM x) (integrable_const _), integral_const] at hmono
  simpa using hmono

theorem aux_eoq_down {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {x y : ℝ}
    (hxy : x ≤ y) : newsvendorCost μ h p x ≤ newsvendorCost μ h p y + p * (y - x) := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0) ∂μ ≤
      ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0 + p * (y - x)) ∂μ :=
    integral_mono (aux_eoq_int hM x) ((aux_eoq_int hM y).add (integrable_const (p * (y - x))))
    (fun ω => by
      have h1 : max (ω - x) 0 ≤ max (ω - y) 0 + (y - x) :=
        max_le (by linarith [le_max_left (ω - y) 0]) (by linarith [le_max_right (ω - y) 0])
      have h2 : max (x - ω) 0 ≤ max (y - ω) 0 := max_le_max (by linarith) le_rfl
      have := mul_le_mul_of_nonneg_left h1 hM.p_pos.le
      have := mul_le_mul_of_nonneg_left h2 hM.h_pos.le
      simp only [Pi.add_apply]
      nlinarith)
  rw [integral_add (aux_eoq_int hM y) (integrable_const _), integral_const] at hmono
  simpa using hmono

theorem aux_eoq_low1 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, h * (y - ω) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
    integral_mono (((integrable_const y).sub hM.integrable).const_mul h) (aux_eoq_int hM y)
    (fun ω => by
      have h1 : y - ω ≤ max (y - ω) 0 := le_max_left _ _
      have h2 : 0 ≤ max (ω - y) 0 := le_max_right _ _
      have := mul_le_mul_of_nonneg_left h1 hM.h_pos.le
      have := mul_nonneg hM.p_pos.le h2
      simp only [Pi.sub_apply]
      nlinarith)
  rw [integral_const_mul, integral_sub (integrable_const _) hM.integrable, integral_const, hM.mean] at hmono
  simpa using hmono

theorem aux_eoq_low2 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, p * (ω - y) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
    integral_mono ((hM.integrable.sub (integrable_const y)).const_mul p) (aux_eoq_int hM y)
    (fun ω => by
      have h1 : ω - y ≤ max (ω - y) 0 := le_max_left _ _
      have h2 : 0 ≤ max (y - ω) 0 := le_max_right _ _
      have := mul_le_mul_of_nonneg_left h1 hM.p_pos.le
      have := mul_nonneg hM.h_pos.le h2
      simp only [Pi.sub_apply]
      nlinarith)
  rw [integral_const_mul, integral_sub hM.integrable (integrable_const _), integral_const, hM.mean] at hmono
  simpa using hmono

theorem aux_eoq_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) := by
  have hL : ∀ x y, |newsvendorCost μ h p x - newsvendorCost μ h p y| ≤ (h + p) * |x - y| := by
    intro x y
    have hh := hM.h_pos
    have hp := hM.p_pos
    rcases le_total x y with hxy | hxy
    · have h1 := aux_eoq_up hM hxy
      have h2 := aux_eoq_down hM hxy
      rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]
      have := mul_nonneg hh.le (sub_nonneg.2 hxy)
      have := mul_nonneg hp.le (sub_nonneg.2 hxy)
      constructor <;> nlinarith
    · have h1 := aux_eoq_up hM hxy
      have h2 := aux_eoq_down hM hxy
      rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_le]
      have := mul_nonneg hh.le (sub_nonneg.2 hxy)
      have := mul_nonneg hp.le (sub_nonneg.2 hxy)
      constructor <;> nlinarith
  have hLip : LipschitzWith (Real.toNNReal (h + p)) (newsvendorCost μ h p) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [hM.h_pos, hM.p_pos])]
      exact hL x y
  exact hLip.continuous


theorem aux_eoq_winlow {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) (r c : ℝ) (hc : ∀ y ∈ Set.Icc r (r + Q), c ≤ newsvendorCost μ h p y) :
    Q * c ≤ ∫ y in r..r + Q, newsvendorCost μ h p y := by
  have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    ((aux_eoq_cont hM).intervalIntegrable (μ := volume) _ _) hc
  simpa using this

theorem aux_eoq_exists {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) : ∃ r, ∀ r', ∫ y in r..r + Q, newsvendorCost μ h p y ≤
      ∫ y in r'..r' + Q, newsvendorCost μ h p y := by
  set G := newsvendorCost μ h p with hGdef
  have hG : Continuous G := aux_eoq_cont hM
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hΦ : Continuous (fun x => ∫ y in (0:ℝ)..x, G y) :=
    intervalIntegral.continuous_primitive (μ := volume) (fun a b => hG.intervalIntegrable a b) 0
  have hφ : Continuous (fun r => ∫ y in r..r + Q, G y) := by
    have : (fun r => ∫ y in r..r + Q, G y) =
        fun r => (∫ y in (0:ℝ)..(r + Q), G y) - ∫ y in (0:ℝ)..r, G y := by
      funext r
      rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)]
    rw [this]
    exact (hΦ.comp (continuous_id.add continuous_const)).sub hΦ
  set m := lam * L
  set φ0 := ∫ y in (0:ℝ)..0 + Q, G y
  refine hφ.exists_forall_le' 0 ?_
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
  constructor
  · rw [Filter.eventually_atBot]
    refine ⟨m - Q - φ0 / (Q * p), fun r hr => ?_⟩
    have hlow := aux_eoq_winlow hM hQ r (p * (m - r - Q)) (fun y hy => by
      have := aux_eoq_low2 hM y
      have : p * (m - r - Q) ≤ p * (m - y) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2]) hp.le
      linarith)
    have h1 : φ0 / (Q * p) ≤ m - r - Q := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    show φ0 ≤ _
    nlinarith
  · rw [Filter.eventually_atTop]
    refine ⟨m + φ0 / (Q * h), fun r hr => ?_⟩
    have hlow := aux_eoq_winlow hM hQ r (h * (r - m)) (fun y hy => by
      have := aux_eoq_low1 hM y
      have : h * (r - m) ≤ h * (y - m) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.1]) hh.le
      linarith)
    have h1 : φ0 / (Q * h) ≤ r - m := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    show φ0 ≤ _
    nlinarith

theorem aux_eoq_reorder {lam L h p K : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) (r' : ℝ) :
    optCost (newsvendorCost μ h p) lam K Q ≤ qrCost (newsvendorCost μ h p) lam K Q r' := by
  obtain ⟨r, hr⟩ := aux_eoq_exists hM hQ
  have hex : ∃ r, IsOptReorder (newsvendorCost μ h p) lam K Q r := ⟨r, fun r'' => by
    unfold qrCost
    exact div_le_div_of_nonneg_right (by linarith [hr r'']) hQ.le⟩
  unfold optCost reorderPt
  rw [dif_pos hex]
  exact hex.choose_spec r'

theorem aux_eoq_affine1 (α p r s : ℝ) :
    ∫ y in r..r + s, (α - p * (y - r)) = α * s - p * s ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => α * y - p * (y - r) ^ 2 / 2)]
  · ring
  · intro x _
    have h1 : HasDerivAt (fun y => α * y - p * (y - r) ^ 2 / 2)
        (α * 1 - p * ((2:ℕ) * (x - r) ^ (2 - 1) * 1) / 2) x :=
      ((hasDerivAt_id' x).const_mul α).sub
        ((((hasDerivAt_id' x).sub_const r).pow 2).const_mul p |>.div_const 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  · exact (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _

theorem aux_eoq_affine2 (β h b u : ℝ) :
    ∫ y in b - u..b, (β - h * (b - y)) = β * u - h * u ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => β * y + h * (b - y) ^ 2 / 2)]
  · ring
  · intro x _
    have h1 : HasDerivAt (fun y => β * y + h * (b - y) ^ 2 / 2)
        (β * 1 + h * ((2:ℕ) * (b - x) ^ (2 - 1) * (-1)) / 2) x :=
      ((hasDerivAt_id' x).const_mul β).add
        ((((hasDerivAt_id' x).const_sub b).pow 2).const_mul h |>.div_const 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  · exact (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _


end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    eoqQty lam K h p ≤ Qs := by
  obtain ⟨hQ, hopt⟩ := hQs
  have hh := hM.h_pos
  have hp := hM.p_pos
  set G := newsvendorCost μ h p with hGdef
  have hG : Continuous G := aux_eoq_cont hM
  set r := reorderPt G lam K Qs with hr
  set I := ∫ y in r..r + Qs, G y with hI
  have keyR : ∀ Δ > 0, lam * K + I ≤ Qs * G (r + Qs) + Qs * h * Δ := by
    intro Δ hΔ
    have h1 := hopt (Qs + Δ) (by positivity)
    have h2 := aux_eoq_reorder (K := K) hM (Q := Qs + Δ) (by positivity) r
    have h3 : ∫ y in r..r + (Qs + Δ), G y ≤ I + Δ * (G (r + Qs) + h * Δ) := by
      rw [← add_assoc, ← intervalIntegral.integral_add_adjacent_intervals (b := r + Qs)
        (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
      have h4 := intervalIntegral.integral_mono_on (μ := volume) (a := r + Qs) (b := r + Qs + Δ) (f := G)
        (g := fun _ => G (r + Qs) + h * Δ) (by linarith) (hG.intervalIntegrable _ _)
        intervalIntegrable_const (fun y hy => by
          have := aux_eoq_up hM hy.1
          have : h * (y - (r + Qs)) ≤ h * Δ :=
            mul_le_mul_of_nonneg_left (by linarith [hy.2]) hh.le
          linarith)
      simp at h4
      linarith
    have h5 : (lam * K + I) / Qs ≤ (lam * K + I + Δ * (G (r + Qs) + h * Δ)) / (Qs + Δ) := by
      calc (lam * K + I) / Qs = optCost G lam K Qs := rfl
        _ ≤ optCost G lam K (Qs + Δ) := h1
        _ ≤ qrCost G lam K (Qs + Δ) r := h2
        _ ≤ _ := by
          unfold qrCost
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    rw [div_le_div_iff₀ hQ (by positivity)] at h5
    have h6 : Δ * (lam * K + I) ≤ Δ * (Qs * G (r + Qs) + Qs * h * Δ) := by nlinarith
    exact le_of_mul_le_mul_left h6 hΔ
  have keyL : ∀ Δ > 0, lam * K + I ≤ Qs * G r + Qs * p * Δ := by
    intro Δ hΔ
    have h1 := hopt (Qs + Δ) (by positivity)
    have h2 := aux_eoq_reorder (K := K) hM (Q := Qs + Δ) (by positivity) (r - Δ)
    have h3 : ∫ y in (r - Δ)..(r - Δ) + (Qs + Δ), G y ≤ I + Δ * (G r + p * Δ) := by
      rw [show r - Δ + (Qs + Δ) = r + Qs by ring,
        ← intervalIntegral.integral_add_adjacent_intervals (b := r)
        (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
      have h4 := intervalIntegral.integral_mono_on (μ := volume) (a := r - Δ) (b := r) (f := G)
        (g := fun _ => G r + p * Δ) (by linarith) (hG.intervalIntegrable _ _)
        intervalIntegrable_const (fun y hy => by
          have := aux_eoq_down hM hy.2
          have : p * (r - y) ≤ p * Δ :=
            mul_le_mul_of_nonneg_left (by linarith [hy.1]) hp.le
          linarith)
      simp at h4
      linarith
    have h5 : (lam * K + I) / Qs ≤ (lam * K + I + Δ * (G r + p * Δ)) / (Qs + Δ) := by
      calc (lam * K + I) / Qs = optCost G lam K Qs := rfl
        _ ≤ optCost G lam K (Qs + Δ) := h1
        _ ≤ qrCost G lam K (Qs + Δ) (r - Δ) := h2
        _ ≤ _ := by
          unfold qrCost
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    rw [div_le_div_iff₀ hQ (by positivity)] at h5
    have h6 : Δ * (lam * K + I) ≤ Δ * (Qs * G r + Qs * p * Δ) := by nlinarith
    exact le_of_mul_le_mul_left h6 hΔ
  have hα : lam * K + I ≤ Qs * G r := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := keyL (ε / (Qs * p)) (by positivity)
    have e : Qs * p * (ε / (Qs * p)) = ε := by field_simp
    linarith
  have hβ : lam * K + I ≤ Qs * G (r + Qs) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := keyR (ε / (Qs * h)) (by positivity)
    have e : Qs * h * (ε / (Qs * h)) = ε := by field_simp
    linarith
  set s := h * Qs / (h + p) with hs
  set u := p * Qs / (h + p) with hu
  have hs' : s * (h + p) = h * Qs := by rw [hs]; field_simp
  have hu' : u * (h + p) = p * Qs := by rw [hu]; field_simp
  have hsu : s + u = Qs := by rw [hs, hu]; field_simp
  have hs0 : 0 ≤ s := by positivity
  have hu0 : 0 ≤ u := by positivity
  have hI1 : G r * s - p * s ^ 2 / 2 ≤ ∫ y in r..r + s, G y := by
    rw [← aux_eoq_affine1 (G r) p r s]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _)
      (hG.intervalIntegrable _ _) (fun y hy => by have := aux_eoq_down hM hy.1; linarith)
  have hI2 : G (r + Qs) * u - h * u ^ 2 / 2 ≤ ∫ y in (r + Qs) - u..r + Qs, G y := by
    rw [← aux_eoq_affine2 (G (r + Qs)) h (r + Qs) u]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _)
      (hG.intervalIntegrable _ _) (fun y hy => by have := aux_eoq_up hM hy.2; linarith)
  have hsplit : I = (∫ y in r..r + s, G y) + ∫ y in (r + Qs) - u..r + Qs, G y := by
    have : r + Qs - u = r + s := by linarith
    rw [this, intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  have hfin : (h + p) * (lam * K) ≤ h * p * Qs ^ 2 / 2 := by
    have e1 := mul_le_mul_of_nonneg_left hα hh.le
    have e2 := mul_le_mul_of_nonneg_left hβ hp.le
    have e3 : (h + p) * (G r * s + G (r + Qs) * u) = Qs * (h * G r + p * G (r + Qs)) := by
      linear_combination G r * hs' + G (r + Qs) * hu'
    have e4 : (h + p) * (p * s ^ 2 + h * u ^ 2) = h * p * Qs ^ 2 := by
      linear_combination p * s * hs' + h * u * hu' + h * p * Qs * hsu
    have e5 : (h + p) * (G r * s - p * s ^ 2 / 2 + (G (r + Qs) * u - h * u ^ 2 / 2)) ≤
        (h + p) * I := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  unfold eoqQty
  rw [Real.sqrt_le_left hQ.le, div_le_iff₀ (by positivity)]
  nlinarith
