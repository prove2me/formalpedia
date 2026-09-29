-- Prove2me | solution 1 for ZhengQR.Flatness.H_scaling_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:35:46.9552+00:00
-- url     : https://prove2.me/submissions/860ea0a8-7fc6-4fb5-80b6-adf544a7a38c

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

open MeasureTheory

theorem aux_hsb_G_def (M : QRModel) (y : ℝ) :
    M.G y = ∫ x, (M.h * max (y - x) 0 + M.p * max (x - y) 0) ∂M.μ := rfl

theorem aux_hsb_integrable (M : QRModel) (y : ℝ) :
    Integrable (fun x : ℝ => M.h * max (y - x) 0 + M.p * max (x - y) 0) M.μ := by
  have := M.isProb
  have h1 : Integrable (fun x : ℝ => y - x) M.μ := (integrable_const y).sub M.integrable
  have h2 : Integrable (fun x : ℝ => x - y) M.μ := M.integrable.sub (integrable_const y)
  exact (h1.pos_part.const_mul _).add (h2.pos_part.const_mul _)

theorem aux_hsb_G_ge_h (M : QRModel) (y : ℝ) : M.h * (y - M.lam * M.L) ≤ M.G y := by
  have := M.isProb
  have hi : Integrable (fun x : ℝ => M.h * (y - x)) M.μ :=
    ((integrable_const y).sub M.integrable).const_mul _
  have : ∫ x, M.h * (y - x) ∂M.μ = M.h * (y - M.lam * M.L) := by
    rw [integral_const_mul, integral_sub (integrable_const y) M.integrable, integral_const,
      M.mean_eq]
    simp
  rw [← this, aux_hsb_G_def]
  apply integral_mono hi (aux_hsb_integrable M y)
  intro x
  have := M.h_pos; have := M.p_pos
  simp only
  nlinarith [le_max_left (y - x) 0, le_max_right (y - x) 0, le_max_left (x - y) 0,
    le_max_right (x - y) 0]

theorem aux_hsb_G_ge_p (M : QRModel) (y : ℝ) : M.p * (M.lam * M.L - y) ≤ M.G y := by
  have := M.isProb
  have hi : Integrable (fun x : ℝ => M.p * (x - y)) M.μ :=
    (M.integrable.sub (integrable_const y)).const_mul _
  have : ∫ x, M.p * (x - y) ∂M.μ = M.p * (M.lam * M.L - y) := by
    rw [integral_const_mul, integral_sub M.integrable (integrable_const y), integral_const,
      M.mean_eq]
    simp
  rw [← this, aux_hsb_G_def]
  apply integral_mono hi (aux_hsb_integrable M y)
  intro x
  have := M.h_pos; have := M.p_pos
  simp only
  nlinarith [le_max_left (y - x) 0, le_max_right (y - x) 0, le_max_left (x - y) 0,
    le_max_right (x - y) 0]

theorem aux_hsb_G_lip (M : QRModel) (y z : ℝ) :
    M.G y ≤ M.G z + (M.h * max (y - z) 0 + M.p * max (z - y) 0) := by
  have := M.isProb
  set c := M.h * max (y - z) 0 + M.p * max (z - y) 0 with hc
  have : M.G z + c = ∫ x, (M.h * max (z - x) 0 + M.p * max (x - z) 0 + c) ∂M.μ := by
    rw [integral_add (aux_hsb_integrable M z) (integrable_const c), integral_const]
    simp [aux_hsb_G_def]
  rw [this, aux_hsb_G_def]
  apply integral_mono (aux_hsb_integrable M y) ((aux_hsb_integrable M z).add (integrable_const c))
  intro x
  have := M.h_pos; have := M.p_pos
  simp only [Pi.add_apply]
  have e1 : max (y - x) 0 ≤ max (z - x) 0 + max (y - z) 0 := by
    apply max_le
    · linarith [le_max_left (z - x) 0, le_max_left (y - z) 0]
    · linarith [le_max_right (z - x) 0, le_max_right (y - z) 0]
  have e2 : max (x - y) 0 ≤ max (x - z) 0 + max (z - y) 0 := by
    apply max_le
    · linarith [le_max_left (x - z) 0, le_max_left (z - y) 0]
    · linarith [le_max_right (x - z) 0, le_max_right (z - y) 0]
  nlinarith

theorem aux_hsb_G_convex (M : QRModel) : ConvexOn ℝ Set.univ M.G := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have := M.isProb
  simp only [smul_eq_mul]
  rw [aux_hsb_G_def, aux_hsb_G_def, aux_hsb_G_def, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_hsb_integrable M x).const_mul a)
      ((aux_hsb_integrable M y).const_mul b)]
  apply integral_mono (aux_hsb_integrable M _)
    (((aux_hsb_integrable M x).const_mul a).add ((aux_hsb_integrable M y).const_mul b))
  intro ξ
  have := M.h_pos; have := M.p_pos
  simp only
  have e1 : max (a * x + b * y - ξ) 0 ≤ a * max (x - ξ) 0 + b * max (y - ξ) 0 := by
    apply max_le
    · have : a * x + b * y - ξ = a * (x - ξ) + b * (y - ξ) := by
        have : ξ = a * ξ + b * ξ := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      nlinarith [le_max_left (x - ξ) 0, le_max_left (y - ξ) 0]
    · have := le_max_right (x - ξ) 0
      have := le_max_right (y - ξ) 0
      positivity
  have e2 : max (ξ - (a * x + b * y)) 0 ≤ a * max (ξ - x) 0 + b * max (ξ - y) 0 := by
    apply max_le
    · have : ξ - (a * x + b * y) = a * (ξ - x) + b * (ξ - y) := by
        have : ξ = a * ξ + b * ξ := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      nlinarith [le_max_left (ξ - x) 0, le_max_left (ξ - y) 0]
    · have := le_max_right (ξ - x) 0
      have := le_max_right (ξ - y) 0
      positivity
  simp only [Pi.add_apply]
  nlinarith

theorem aux_hsb_G_cont (M : QRModel) : Continuous M.G := by
  have hL : LipschitzWith (Real.toNNReal (M.h + M.p)) M.G := by
    apply LipschitzWith.of_le_add_mul'
    intro y z
    have := aux_hsb_G_lip M y z
    have := M.h_pos; have := M.p_pos
    rw [Real.dist_eq]
    have h1 : max (y - z) 0 ≤ |y - z| := max_le (le_abs_self _) (abs_nonneg _)
    have h2 : max (z - y) 0 ≤ |y - z| := by
      rw [abs_sub_comm]; exact max_le (le_abs_self _) (abs_nonneg _)
    nlinarith
  exact hL.continuous

theorem aux_hsb_F_deriv (M : QRModel) (Q r : ℝ) :
    HasDerivAt (fun r => ∫ y in r..r + Q, M.G y) (M.G (r + Q) - M.G r) r := by
  have hc := aux_hsb_G_cont M
  have hfun : (fun r => ∫ y in r..r + Q, M.G y) =
      fun r => (∫ y in (0:ℝ)..r + Q, M.G y) - ∫ y in (0:ℝ)..r, M.G y := by
    funext r
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [hfun]
  have h1 : HasDerivAt (fun r => ∫ y in (0:ℝ)..r + Q, M.G y) (M.G (r + Q)) r := by
    have := (hc.integral_hasStrictDerivAt 0 (r + Q)).hasDerivAt
    have h2 : HasDerivAt (fun r : ℝ => r + Q) 1 r := (hasDerivAt_id r).add_const Q
    have h3 := this.comp r h2
    rw [mul_one] at h3
    exact h3
  exact h1.sub (hc.integral_hasStrictDerivAt 0 r).hasDerivAt

theorem aux_hsb_F_lower (M : QRModel) (Q : ℝ) (hQ : 0 < Q) (r : ℝ) :
    Q * max (M.h * (r - M.lam * M.L)) (M.p * (M.lam * M.L - (r + Q))) ≤
      ∫ y in r..r + Q, M.G y := by
  have hc := aux_hsb_G_cont M
  have hle : r ≤ r + Q := by linarith
  have key : ∀ c : ℝ, (∀ y ∈ Set.Icc r (r + Q), c ≤ M.G y) → Q * c ≤ ∫ y in r..r + Q, M.G y := by
    intro c hcy
    have := intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const : IntervalIntegrable (fun _ => c) volume r (r + Q))
      (hc.intervalIntegrable _ _) hcy
    simpa using this
  have := M.h_pos; have := M.p_pos
  rcases le_total (M.h * (r - M.lam * M.L)) (M.p * (M.lam * M.L - (r + Q))) with h | h
  · rw [max_eq_right h]
    apply key
    intro y hy
    have := aux_hsb_G_ge_p M y
    nlinarith [hy.2]
  · rw [max_eq_left h]
    apply key
    intro y hy
    have := aux_hsb_G_ge_h M y
    nlinarith [hy.1]

theorem aux_hsb_exists_min (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    ∃ r, ∀ r', (∫ y in r..r + Q, M.G y) ≤ ∫ y in r'..r' + Q, M.G y := by
  apply Continuous.exists_forall_le
  · exact continuous_iff_continuousAt.2 fun r => (aux_hsb_F_deriv M Q r).continuousAt
  · rw [cocompact_eq_atBot_atTop, Filter.tendsto_sup]
    have := M.h_pos; have := M.p_pos
    constructor
    · rw [Filter.tendsto_atBot_atTop]
      intro B
      refine ⟨M.lam * M.L - Q - |B| / (Q * M.p), fun r hr => ?_⟩
      have h1 := aux_hsb_F_lower M Q hQ r
      have h2 := le_max_right (M.h * (r - M.lam * M.L)) (M.p * (M.lam * M.L - (r + Q)))
      have h3 : |B| / (Q * M.p) ≤ M.lam * M.L - (r + Q) := by linarith
      have h4 : |B| ≤ Q * M.p * (M.lam * M.L - (r + Q)) := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at h3
      have h5 := le_abs_self B
      nlinarith
    · rw [Filter.tendsto_atTop_atTop]
      intro B
      refine ⟨M.lam * M.L + |B| / (Q * M.h), fun r hr => ?_⟩
      have h1 := aux_hsb_F_lower M Q hQ r
      have h2 := le_max_left (M.h * (r - M.lam * M.L)) (M.p * (M.lam * M.L - (r + Q)))
      have h3 : |B| / (Q * M.h) ≤ r - M.lam * M.L := by linarith
      have h4 : |B| ≤ Q * M.h * (r - M.lam * M.L) := by
        rwa [div_le_iff₀ (by positivity), mul_comm] at h3
      have h5 := le_abs_self B
      nlinarith

theorem aux_hsb_H_spec (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    ∃ r, M.H Q = M.G r ∧ M.G (r + Q) = M.G r := by
  have hex : ∃ r, IsOptReorder M.G M.lam M.K Q r := by
    obtain ⟨r, hr⟩ := aux_hsb_exists_min M Q hQ
    refine ⟨r, fun r' => ?_⟩
    unfold qrCost
    apply div_le_div_of_nonneg_right _ hQ.le
    linarith [hr r']
  refine ⟨optReorder M.G M.lam M.K Q, ?_, ?_⟩
  · simp only [QRModel.H, Hfun, if_pos hQ]
  · have hspec : IsOptReorder M.G M.lam M.K Q (optReorder M.G M.lam M.K Q) := by
      unfold optReorder
      rw [dif_pos hex]
      exact hex.choose_spec
    set r := optReorder M.G M.lam M.K Q
    have hmin : ∀ r', (∫ y in r..r + Q, M.G y) ≤ ∫ y in r'..r' + Q, M.G y := by
      intro r'
      have := hspec r'
      unfold qrCost at this
      have := (div_le_div_iff_of_pos_right hQ).1 this
      linarith
    have hloc : IsLocalMin (fun r => ∫ y in r..r + Q, M.G y) r :=
      Filter.Eventually.of_forall hmin
    have := hloc.hasDerivAt_eq_zero (aux_hsb_F_deriv M Q r)
    linarith

theorem aux_hsb_part1 (M : QRModel) (Q : ℝ) (hQ : 0 < Q) (α : ℝ) (hα : 1 < α) :
    M.H (α * Q) ≤ α * M.H Q := by
  obtain ⟨r, hHQ, hr⟩ := aux_hsb_H_spec M Q hQ
  have hαQ : 0 < α * Q := by positivity
  obtain ⟨s, hHs, hs⟩ := aux_hsb_H_spec M (α * Q) hαQ
  have hp := M.p_pos
  have hh := M.h_pos
  set t := M.G r with ht
  set m := M.lam * M.L with hm
  have l1 : M.p * (m - r) ≤ t := aux_hsb_G_ge_p M r
  have l2 : M.h * (r + Q - m) ≤ t := by rw [← hr]; exact aux_hsb_G_ge_h M (r + Q)
  -- t * (h + p) ≥ Q * h * p
  have key : Q * (M.h * M.p) ≤ t * (M.h + M.p) := by nlinarith
  have tpos : 0 ≤ t := by
    have h0 : 0 < t * (M.h + M.p) := lt_of_lt_of_le (by positivity) key
    nlinarith
  set u := (α - 1) * t / M.p with hu
  set v := (α - 1) * t / M.h with hv
  have hpu : M.p * u = (α - 1) * t := by rw [hu]; field_simp
  have hhv : M.h * v = (α - 1) * t := by rw [hv]; field_simp
  have u0 : 0 ≤ u := by rw [hu]; apply div_nonneg _ hp.le; nlinarith
  have v0 : 0 ≤ v := by rw [hv]; apply div_nonneg _ hh.le; nlinarith
  have width : (α - 1) * Q ≤ u + v := by
    have e : (M.h * M.p) * (u + v) = (α - 1) * t * (M.h + M.p) := by
      have : (M.h * M.p) * (u + v) = M.h * (M.p * u) + M.p * (M.h * v) := by ring
      rw [this, hpu, hhv]; ring
    have e2 : (M.h * M.p) * ((α - 1) * Q) ≤ (M.h * M.p) * (u + v) := by
      rw [e]; nlinarith
    exact le_of_mul_le_mul_left e2 (by positivity)
  set a := r - u with ha
  set b := r + Q + v with hb
  have Ga : M.G a ≤ α * t := by
    have := aux_hsb_G_lip M a r
    rw [max_eq_right (by linarith : a - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - a)] at this
    have : r - a = u := by rw [ha]; ring
    nlinarith
  have Gb : M.G b ≤ α * t := by
    have := aux_hsb_G_lip M b (r + Q)
    rw [max_eq_left (by linarith : 0 ≤ b - (r + Q)), max_eq_right (by linarith : r + Q - b ≤ 0),
      hr] at this
    have : b - (r + Q) = v := by rw [hb]; ring
    nlinarith
  have hconv := aux_hsb_G_convex M
  have Gab : M.G (a + α * Q) ≤ α * t := by
    have hmem : a + α * Q ∈ segment ℝ a b := by
      rw [segment_eq_Icc (by linarith)]
      constructor <;> nlinarith
    have := hconv.le_on_segment (Set.mem_univ a) (Set.mem_univ b) hmem
    exact this.trans (max_le Ga Gb)
  -- lower bound: G s ≤ max (G a) (G (a + αQ))
  have low : M.G s ≤ max (M.G a) (M.G (a + α * Q)) := by
    rcases lt_trichotomy a s with h | h | h
    · have := hconv.slope_mono_adjacent (Set.mem_univ a) (Set.mem_univ (s + α * Q)) h
        (by linarith : s < s + α * Q)
      rw [hs, sub_self, zero_div] at this
      have hsa : 0 < s - a := by linarith
      have h2 : M.G s - M.G a ≤ 0 * (s - a) := (div_le_iff₀ hsa).1 this
      exact le_max_of_le_left (by linarith)
    · rw [h]; exact le_max_left _ _
    · have := hconv.slope_mono_adjacent (Set.mem_univ s) (Set.mem_univ (a + α * Q))
        (by linarith : s < s + α * Q) (by linarith : s + α * Q < a + α * Q)
      rw [hs, sub_self, zero_div] at this
      have hpos : 0 < a + α * Q - (s + α * Q) := by linarith
      have h2 : 0 * (a + α * Q - (s + α * Q)) ≤ M.G (a + α * Q) - M.G s :=
        (le_div_iff₀ hpos).1 this
      exact le_max_of_le_right (by linarith)
  rw [hHs, hHQ]
  exact low.trans (max_le Ga Gab)

end ZhengQR.Flatness

open ZhengQR.Flatness

theorem solution (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∀ α : ℝ, 1 < α → M.H (α * Q) ≤ α * M.H Q) ∧
      (∀ α : ℝ, 0 < α → α < 1 → α * M.H Q ≤ M.H (α * Q)) := by
  refine ⟨fun α hα => aux_hsb_part1 M Q hQ α hα, fun α hα0 hα1 => ?_⟩
  have hαQ : 0 < α * Q := by positivity
  have h1 : 1 < 1 / α := by rw [lt_div_iff₀ hα0]; linarith
  have := aux_hsb_part1 M (α * Q) hαQ (1 / α) h1
  have e : 1 / α * (α * Q) = Q := by field_simp
  rw [e] at this
  have := mul_le_mul_of_nonneg_left this hα0.le
  have e2 : α * (1 / α * M.H (α * Q)) = M.H (α * Q) := by field_simp
  linarith
