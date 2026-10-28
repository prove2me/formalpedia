-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P08.globalDepolarizingOptimizer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T12:05:19.917314+00:00
-- url     : https://prove2.me/submissions/805be7ec-aa8a-4ded-80ed-6730df30f474

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P08

namespace S202GD

open Real intervalIntegral

noncomputable def gI (a b r t : ℝ) : ℝ :=
  a ^ 2 / (1 - (1 - a ^ 2 + a ^ 2 * r ^ 2) * t ^ 2) - b ^ 2 / (1 - b ^ 2 * r ^ 2 * t ^ 2)

noncomputable def G (a b r : ℝ) : ℝ := ∫ t in (0:ℝ)..1, gI a b r t

lemma J_closed (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    ∫ t in (0:ℝ)..1, 1 / (1 - x ^ 2 * t ^ 2) =
      (Real.log (1 + x) - Real.log (1 - x)) / (2 * x) := by
  have hF : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt
      (fun t => (Real.log (1 + x * t) - Real.log (1 - x * t)) / (2 * x))
      (1 / (1 - x ^ 2 * t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1 : 0 < 1 + x * t := by nlinarith
    have h2 : 0 < 1 - x * t := by nlinarith
    have d1 : HasDerivAt (fun t => 1 + x * t) x t := by
      simpa using ((hasDerivAt_id t).const_mul x).const_add 1
    have d2 : HasDerivAt (fun t => 1 - x * t) (-x) t := by
      simpa using ((hasDerivAt_id t).const_mul x).const_sub 1
    have := ((d1.log h1.ne').sub (d2.log h2.ne')).div_const (2 * x)
    refine this.congr_deriv ?_
    have h3 : 1 - x ^ 2 * t ^ 2 = (1 + x * t) * (1 - x * t) := by ring
    rw [h3]
    field_simp
    ring
  have hint : IntervalIntegrable (fun t => 1 / (1 - x ^ 2 * t ^ 2)) MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have : x ^ 2 * t ^ 2 < 1 := by
      have : x * t < 1 := by nlinarith
      nlinarith [mul_nonneg hx0.le ht0]
    linarith
  rw [integral_eq_sub_of_hasDerivAt hF hint]
  simp

section
variable {a b : ℝ}

lemma cpos (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr1 : r < 1) (hr0 : 0 ≤ r) :
    0 < 1 - (1 - a ^ 2 + a ^ 2 * r ^ 2) := by
  have : r ^ 2 < 1 := by nlinarith
  nlinarith [sq_pos_of_pos ha]

lemma gI_cont (ha : 0 < a) (ha1 : a < 1) (hb : b < 1) (hb0 : 0 < b) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) : ContinuousOn (gI a b r) (Set.uIcc 0 1) := by
  rw [Set.uIcc_of_le zero_le_one]
  have hc := cpos ha ha1 hr1 hr0
  have hc0 : 0 ≤ 1 - a ^ 2 + a ^ 2 * r ^ 2 := by nlinarith [sq_nonneg (a * r)]
  unfold gI
  apply ContinuousOn.sub
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ⟨ht0, ht1⟩
    have : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hc0]
  · apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t ⟨ht0, ht1⟩
    have : t ^ 2 ≤ 1 := by nlinarith
    have : r ^ 2 < 1 := by nlinarith
    have : b ^ 2 < 1 := by nlinarith
    have : b ^ 2 * r ^ 2 < 1 := by nlinarith [sq_nonneg b]
    nlinarith [mul_le_mul_of_nonneg_left (show t ^ 2 ≤ 1 by assumption)
      (mul_nonneg (sq_nonneg b) (sq_nonneg r))]

noncomputable def P (a b r τ : ℝ) : ℝ := (1 - (1 - a ^ 2 + a ^ 2 * r ^ 2) * τ) * (1 - b ^ 2 * r ^ 2 * τ)

lemma gI_eq (a b r t τ0 : ℝ) (hτ : b ^ 2 * (1 - a ^ 2) * τ0 = b ^ 2 - a ^ 2)
    (p1 : 1 - (1 - a ^ 2 + a ^ 2 * r ^ 2) * t ^ 2 ≠ 0) (p2 : 1 - b ^ 2 * r ^ 2 * t ^ 2 ≠ 0) :
    gI a b r t = b ^ 2 * (1 - a ^ 2) * (t ^ 2 - τ0) / P a b r (t ^ 2) := by
  unfold gI P
  rw [div_sub_div _ _ p1 p2]
  congr 1
  linear_combination hτ

lemma gen_pt (N P1 P2 P1' P2' : ℝ) (h1 : P1 ≠ 0) (h2 : P2 ≠ 0) (h2' : P2' ≠ 0) :
    N / P2 - P1' / P2' * (N / P1) = N * (P1 * P2' - P1' * P2) / (P1 * P2 * P2') := by
  field_simp

lemma P_diff (a b r1 r2 τ τ0 : ℝ) :
    P a b r1 τ * P a b r2 τ0 - P a b r1 τ0 * P a b r2 τ =
      (τ - τ0) * ((a ^ 2 * r2 ^ 2 - a ^ 2 * r1 ^ 2) * (1 - b ^ 2 * r1 ^ 2 * τ) *
            (1 - b ^ 2 * r2 ^ 2 * τ0) +
          (1 - (1 - a ^ 2 + a ^ 2 * r1 ^ 2) * τ0) * (1 - (1 - a ^ 2 + a ^ 2 * r2 ^ 2) * τ) *
            (b ^ 2 * r2 ^ 2 - b ^ 2 * r1 ^ 2)) := by
  unfold P; ring

lemma A_pos (ha : 0 < a) (ha1 : a < 1) {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) : 0 < 1 - (1 - a ^ 2 + a ^ 2 * r ^ 2) * τ := by
  have hc := cpos ha ha1 hr1 hr0
  have hc0 : 0 ≤ 1 - a ^ 2 + a ^ 2 * r ^ 2 := by nlinarith [sq_nonneg (a * r)]
  nlinarith [mul_le_mul_of_nonneg_left hτ1 hc0]

lemma B_pos (hb0 : 0 < b) (hb : b < 1) {r τ : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hτ0 : 0 ≤ τ)
    (hτ1 : τ ≤ 1) : 0 < 1 - b ^ 2 * r ^ 2 * τ := by
  have : r ^ 2 < 1 := by nlinarith
  have : b ^ 2 < 1 := by nlinarith
  have : b ^ 2 * r ^ 2 < 1 := by nlinarith [sq_nonneg b]
  nlinarith [mul_le_mul_of_nonneg_left hτ1 (mul_nonneg (sq_nonneg b) (sq_nonneg r))]

lemma P_pos (ha : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb : b < 1) {r τ : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) : 0 < P a b r τ :=
  mul_pos (A_pos ha ha1 hr0 hr1 hτ0 hτ1) (B_pos hb0 hb hr0 hr1 hτ0 hτ1)

lemma key (ha : 0 < a) (hab : a < b) (hb : b < 1) {r1 r2 : ℝ} (h0 : 0 ≤ r1) (h12 : r1 < r2)
    (h2 : r2 < 1) (hG : 0 ≤ G a b r1) : 0 < G a b r2 := by
  have ha1 : a < 1 := by linarith
  have hb0 : 0 < b := by linarith
  have hr2 : 0 ≤ r2 := by linarith
  have hr1 : r1 < 1 := by linarith
  set τ0 := (b ^ 2 - a ^ 2) / (b ^ 2 * (1 - a ^ 2)) with hτ0def
  have hden : 0 < b ^ 2 * (1 - a ^ 2) := by
    have : a ^ 2 < 1 := by nlinarith
    have := sq_pos_of_pos hb0
    nlinarith
  have hτ : b ^ 2 * (1 - a ^ 2) * τ0 = b ^ 2 - a ^ 2 := by
    rw [hτ0def]; exact mul_div_cancel₀ _ hden.ne'
  have hτpos : 0 < τ0 := by
    apply div_pos _ hden
    nlinarith
  have hτ1 : τ0 < 1 := by
    rw [div_lt_one hden]
    have : 0 < 1 - b ^ 2 := by nlinarith
    nlinarith [mul_pos (sq_pos_of_pos ha) this]
  set ρ0 := P a b r1 τ0 / P a b r2 τ0 with hρ0
  have hP1' := P_pos ha ha1 hb0 hb h0 hr1 hτpos.le hτ1.le
  have hP2' := P_pos ha ha1 hb0 hb hr2 h2 hτpos.le hτ1.le
  have hρpos : 0 < ρ0 := div_pos hP1' hP2'
  have hi1 := (gI_cont ha ha1 hb hb0 h0 hr1).intervalIntegrable (μ := MeasureTheory.volume)
  have hi2 := (gI_cont ha ha1 hb hb0 hr2 h2).intervalIntegrable (μ := MeasureTheory.volume)
  set h := fun t => gI a b r2 t - ρ0 * gI a b r1 t with hh
  have hint : ∫ t in (0:ℝ)..1, h t = G a b r2 - ρ0 * G a b r1 := by
    simp only [hh]
    rw [intervalIntegral.integral_sub hi2 (hi1.const_mul ρ0), intervalIntegral.integral_const_mul]
    rfl
  have hhi : IntervalIntegrable h MeasureTheory.volume 0 1 := hi2.sub (hi1.const_mul ρ0)
  -- pointwise
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ h t ∧ (t ^ 2 ≠ τ0 → 0 < h t) := by
    intro t ⟨ht0, ht1⟩
    have hτt0 : 0 ≤ t ^ 2 := sq_nonneg t
    have hτt1 : t ^ 2 ≤ 1 := by nlinarith
    have A1 := A_pos ha ha1 h0 hr1 hτt0 hτt1
    have A2 := A_pos ha ha1 hr2 h2 hτt0 hτt1
    have B1 := B_pos hb0 hb h0 hr1 hτt0 hτt1
    have B2 := B_pos hb0 hb hr2 h2 hτt0 hτt1
    have A1' := A_pos ha ha1 h0 hr1 hτpos.le hτ1.le
    have B2' := B_pos hb0 hb hr2 h2 hτpos.le hτ1.le
    have hP1 := P_pos ha ha1 hb0 hb h0 hr1 hτt0 hτt1
    have hP2 := P_pos ha ha1 hb0 hb hr2 h2 hτt0 hτt1
    have e : h t = b ^ 2 * (1 - a ^ 2) * (t ^ 2 - τ0) *
        (P a b r1 (t ^ 2) * P a b r2 τ0 - P a b r1 τ0 * P a b r2 (t ^ 2)) /
        (P a b r1 (t ^ 2) * P a b r2 (t ^ 2) * P a b r2 τ0) := by
      simp only [hh]
      rw [gI_eq a b r2 t τ0 hτ A2.ne' B2.ne', gI_eq a b r1 t τ0 hτ A1.ne' B1.ne', hρ0]
      exact gen_pt _ _ _ _ _ hP1.ne' hP2.ne' hP2'.ne'
    rw [P_diff] at e
    set K := ((a ^ 2 * r2 ^ 2 - a ^ 2 * r1 ^ 2) * (1 - b ^ 2 * r1 ^ 2 * t ^ 2) *
            (1 - b ^ 2 * r2 ^ 2 * τ0) +
          (1 - (1 - a ^ 2 + a ^ 2 * r1 ^ 2) * τ0) * (1 - (1 - a ^ 2 + a ^ 2 * r2 ^ 2) * t ^ 2) *
            (b ^ 2 * r2 ^ 2 - b ^ 2 * r1 ^ 2)) with hK
    have hK : 0 < K := by
      have hrr : 0 < r2 ^ 2 - r1 ^ 2 := by
        have : r2 ^ 2 - r1 ^ 2 = (r2 - r1) * (r2 + r1) := by ring
        rw [this]; exact mul_pos (by linarith) (by linarith)
      have d1 : 0 < a ^ 2 * r2 ^ 2 - a ^ 2 * r1 ^ 2 := by
        have := mul_pos (sq_pos_of_pos ha) hrr
        linarith [show a ^ 2 * (r2 ^ 2 - r1 ^ 2) = a ^ 2 * r2 ^ 2 - a ^ 2 * r1 ^ 2 by ring]
      have d2 : 0 ≤ b ^ 2 * r2 ^ 2 - b ^ 2 * r1 ^ 2 := by
        have := mul_nonneg (sq_nonneg b) hrr.le
        linarith [show b ^ 2 * (r2 ^ 2 - r1 ^ 2) = b ^ 2 * r2 ^ 2 - b ^ 2 * r1 ^ 2 by ring]
      have := mul_pos (mul_pos d1 B1) B2'
      have := mul_nonneg (mul_pos A1' A2).le d2
      linarith
    have hD : 0 < P a b r1 (t ^ 2) * P a b r2 (t ^ 2) * P a b r2 τ0 :=
      mul_pos (mul_pos hP1 hP2) hP2'
    rw [e]
    have en : b ^ 2 * (1 - a ^ 2) * (t ^ 2 - τ0) * ((t ^ 2 - τ0) * K) =
        b ^ 2 * (1 - a ^ 2) * (t ^ 2 - τ0) ^ 2 * K := by ring
    rw [en]
    refine ⟨div_nonneg (mul_nonneg (mul_nonneg hden.le (sq_nonneg _)) hK.le) hD.le, fun hne => ?_⟩
    have : 0 < (t ^ 2 - τ0) ^ 2 := by
      have : t ^ 2 - τ0 ≠ 0 := sub_ne_zero.mpr hne
      positivity
    exact div_pos (mul_pos (mul_pos hden this) hK) hD
  set m := (1 + τ0) / 2 with hm
  have hm0 : 0 ≤ m := by linarith
  have hm1 : m < 1 := by linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hhi.mono_set (by rw [Set.uIcc_of_le hm0, Set.uIcc_of_le zero_le_one]
                      exact Set.Icc_subset_Icc le_rfl hm1.le))
    (hhi.mono_set (by rw [Set.uIcc_of_le hm1.le, Set.uIcc_of_le zero_le_one]
                      exact Set.Icc_subset_Icc hm0 le_rfl))
  have I1 : 0 ≤ ∫ t in (0:ℝ)..m, h t :=
    intervalIntegral.integral_nonneg hm0 (fun t ht => (hpt t ⟨ht.1, by linarith [ht.2]⟩).1)
  have I2 : 0 < ∫ t in m..1, h t := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hhi.mono_set (by rw [Set.uIcc_of_le hm1.le, Set.uIcc_of_le zero_le_one]
                        exact Set.Icc_subset_Icc hm0 le_rfl)) _ hm1
    intro t ⟨ht0, ht1⟩
    apply (hpt t ⟨by linarith, ht1.le⟩).2
    have : m ^ 2 < t ^ 2 := by nlinarith
    have : τ0 < m ^ 2 := by nlinarith [sq_nonneg (1 - τ0)]
    intro heq; linarith
  have : 0 < G a b r2 - ρ0 * G a b r1 := by
    rw [← hint, ← hsplit]; linarith
  nlinarith [mul_nonneg hρpos.le hG]
end


noncomputable def J (x : ℝ) : ℝ := ∫ t in (0:ℝ)..1, 1 / (1 - x ^ 2 * t ^ 2)

lemma J_int {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    IntervalIntegrable (fun t => 1 / (1 - x ^ 2 * t ^ 2)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  obtain ⟨ht0, ht1⟩ := ht
  have : x * t < 1 := by nlinarith
  have : x ^ 2 * t ^ 2 < 1 := by nlinarith [mul_nonneg hx0 ht0]
  linarith

lemma J_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) : J x ≤ 1 / (1 - x ^ 2) := by
  have h := intervalIntegral.integral_mono_on zero_le_one (J_int hx0 hx1)
    (intervalIntegrable_const (c := 1 / (1 - x ^ 2)))
    (fun t ⟨ht0, ht1⟩ => by
      have hx2 : x ^ 2 < 1 := by nlinarith
      have : t ^ 2 ≤ 1 := by nlinarith
      apply one_div_le_one_div_of_le (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left this (sq_nonneg x)])
  simpa [J] using h

lemma J_zero : J 0 = 1 := by simp [J]

section
variable {a b : ℝ}

lemma s_facts (ha : 0 < a) (ha1 : a < 1) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < √(1 - a ^ 2 + a ^ 2 * r ^ 2) ∧ √(1 - a ^ 2 + a ^ 2 * r ^ 2) < 1 ∧
      √(1 - a ^ 2 + a ^ 2 * r ^ 2) ^ 2 = 1 - a ^ 2 + a ^ 2 * r ^ 2 := by
  have hc := cpos ha ha1 hr1 hr0
  have hc0 : 0 < 1 - a ^ 2 + a ^ 2 * r ^ 2 := by
    have : a ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (a * r)]
  refine ⟨Real.sqrt_pos.mpr hc0, ?_, Real.sq_sqrt hc0.le⟩
  rw [Real.sqrt_lt' one_pos]; linarith

lemma G_J (ha : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb : b < 1) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    G a b r = a ^ 2 * J (√(1 - a ^ 2 + a ^ 2 * r ^ 2)) - b ^ 2 * J (b * r) := by
  obtain ⟨hs0, hs1, hs2⟩ := s_facts ha ha1 hr0 hr1
  have hbr0 : 0 ≤ b * r := mul_nonneg hb0.le hr0
  have hbr1 : b * r < 1 := by nlinarith
  unfold G J
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub ((J_int hs0.le hs1).const_mul _)
      ((J_int hbr0 hbr1).const_mul _)]
  congr 1
  funext t
  unfold gI
  rw [hs2]
  ring

lemma J_lower {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : -Real.log (1 - x) / 2 ≤ J x := by
  unfold J
  rw [J_closed x hx0 hx1]
  have h1 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have h2 : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by norm_num) (by linarith)]
  nlinarith

lemma exists_pos (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ r, 0 < r ∧ r < 1 ∧ 0 < G a b r := by
  have ha1 : a < 1 := by linarith
  have hb0 : 0 < b := by linarith
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  set M := b ^ 2 / (1 - b ^ 2) with hM
  set K := 2 * M / a ^ 2 + 1 with hK
  set δ := min (1 / 2) (Real.exp (-K) / (2 * a ^ 2)) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ Real.exp (-K) / (2 * a ^ 2) := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  have hr0 : 0 ≤ 1 - δ := by linarith
  have hr1 : 1 - δ < 1 := by linarith
  rw [G_J ha ha1 hb0 hb hr0 hr1]
  obtain ⟨hs0, hs1, hs2⟩ := s_facts ha ha1 hr0 hr1
  set s := √(1 - a ^ 2 + a ^ 2 * (1 - δ) ^ 2)
  have hJb : J (b * (1 - δ)) ≤ 1 / (1 - b ^ 2) := by
    have h0 : 0 ≤ b * (1 - δ) := by positivity
    have h1 : b * (1 - δ) < 1 := by nlinarith
    refine (J_le h0 h1).trans (one_div_le_one_div_of_le hb2 ?_)
    have : b * (1 - δ) ≤ b := by nlinarith
    nlinarith
  have h1s : 1 - s ≤ Real.exp (-K) := by
    have e1 : 1 - s ≤ 1 - s ^ 2 := by nlinarith
    have e2 : 1 - s ^ 2 = a ^ 2 * δ * (2 - δ) := by rw [hs2]; ring
    have e3 : a ^ 2 * δ * (2 - δ) ≤ 2 * a ^ 2 * δ := by nlinarith
    have e4 : 2 * a ^ 2 * δ ≤ Real.exp (-K) := by
      rw [le_div_iff₀ (by positivity)] at hδ2; linarith
    linarith
  have hlog : K ≤ -Real.log (1 - s) := by
    have := Real.log_le_log (by linarith) h1s
    rw [Real.log_exp] at this; linarith
  have hJs := J_lower hs0 hs1
  have : a ^ 2 * (K / 2) = M + a ^ 2 / 2 := by
    rw [hK]; field_simp
  have hJs' : M + a ^ 2 / 2 ≤ a ^ 2 * J s := by
    rw [← this]
    apply mul_le_mul_of_nonneg_left _ ha2.le
    linarith
  have : b ^ 2 * J (b * (1 - δ)) ≤ M := by
    have := mul_le_mul_of_nonneg_left hJb (sq_nonneg b)
    rw [hM]; rw [mul_one_div] at this; exact this
  linarith

lemma G_contOn (ha : 0 < a) (ha1 : a < 1) (hb0 : 0 < b) (hb : b < 1) {R : ℝ} (hR0 : 0 ≤ R)
    (hR1 : R < 1) : ContinuousOn (G a b) (Set.Icc 0 R) := by
  set cR := 1 - a ^ 2 + a ^ 2 * R ^ 2
  set eR := b ^ 2 * R ^ 2
  have hcR := cpos ha ha1 hR1 hR0
  have hcR0 : 0 ≤ cR := by
    have : a ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg (a * R)]
  have heR : eR < 1 := by
    have : R ^ 2 < 1 := by nlinarith
    have : b ^ 2 < 1 := by nlinarith
    nlinarith [sq_nonneg b]
  let f : ℝ → ℝ → ℝ := fun r t =>
    a ^ 2 / (1 - min (1 - a ^ 2 + a ^ 2 * r ^ 2) cR * min (t ^ 2) 1) -
      b ^ 2 / (1 - min (b ^ 2 * r ^ 2) eR * min (t ^ 2) 1)
  have hcont : Continuous (Function.uncurry f) := by
    apply Continuous.sub
    · apply Continuous.div continuous_const (by fun_prop)
      intro x
      have h1 : min (1 - a ^ 2 + a ^ 2 * x.1 ^ 2) cR ≤ cR := min_le_right _ _
      have h2 : min (x.2 ^ 2) 1 ≤ 1 := min_le_right _ _
      have h3 : 0 ≤ min (x.2 ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
      have h4 : 0 ≤ min (1 - a ^ 2 + a ^ 2 * x.1 ^ 2) cR := by
        have : a ^ 2 < 1 := by nlinarith
        exact le_min (by nlinarith [sq_nonneg (a * x.1)]) hcR0
      have := mul_le_mul h1 h2 h3 hcR0
      intro h; linarith
    · apply Continuous.div continuous_const (by fun_prop)
      intro x
      have h1 : min (b ^ 2 * x.1 ^ 2) eR ≤ eR := min_le_right _ _
      have h2 : min (x.2 ^ 2) 1 ≤ 1 := min_le_right _ _
      have h3 : 0 ≤ min (x.2 ^ 2) 1 := le_min (sq_nonneg _) zero_le_one
      have h4 : 0 ≤ min (b ^ 2 * x.1 ^ 2) eR := le_min (by positivity) (by positivity)
      have := mul_le_mul h1 h2 h3 (by positivity)
      intro h; linarith
  have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := MeasureTheory.volume) hcont 0 1
  refine hc.continuousOn.congr ?_
  intro r ⟨hr0, hr1⟩
  unfold G
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have hrR : r ^ 2 ≤ R ^ 2 := by nlinarith
  have m1 : min (1 - a ^ 2 + a ^ 2 * r ^ 2) cR = 1 - a ^ 2 + a ^ 2 * r ^ 2 :=
    min_eq_left (by nlinarith [sq_nonneg a])
  have m2 : min (b ^ 2 * r ^ 2) eR = b ^ 2 * r ^ 2 :=
    min_eq_left (by nlinarith [sq_nonneg b])
  have m3 : min (t ^ 2) 1 = t ^ 2 := min_eq_left (by nlinarith [ht.1, ht.2])
  simp only [f, gI, m1, m2, m3]

end

section
variable {a b : ℝ}

lemma log_half (x : ℝ) (hx : 0 < x) : Real.log (x / 2) = Real.log x - Real.log 2 :=
  Real.log_div hx.ne' two_ne_zero

lemma F_deriv (ha : 0 < a) (hab : a < b) (hb : b < 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    HasDerivAt (fun r => QAlgorithms.binEntropy2 ((1 + b * r) / 2) -
        QAlgorithms.binEntropy2 ((1 + √(1 - a ^ 2 + a ^ 2 * r ^ 2)) / 2))
      (r * G a b r / Real.log 2) r := by
  have ha1 : a < 1 := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨hs0, hs1, hs2⟩ := s_facts ha ha1 hr0.le hr1
  set s := √(1 - a ^ 2 + a ^ 2 * r ^ 2) with hs
  have hbr0 : 0 < b * r := mul_pos hb0 hr0
  have hbr1 : b * r < 1 := by nlinarith
  have hc0 : 0 < 1 - a ^ 2 + a ^ 2 * r ^ 2 := by nlinarith
  have hq1 : HasDerivAt (fun r => (1 + b * r) / 2) (b / 2) r := by
    simpa using (((hasDerivAt_id r).const_mul b).const_add 1).div_const 2
  have hcd : HasDerivAt (fun r => 1 - a ^ 2 + a ^ 2 * r ^ 2) (a ^ 2 * (2 * r)) r := by
    simpa using ((hasDerivAt_pow 2 r).const_mul (a ^ 2)).const_add (1 - a ^ 2)
  have hsd := hcd.sqrt hc0.ne'
  have hq2 : HasDerivAt (fun r => (1 + √(1 - a ^ 2 + a ^ 2 * r ^ 2)) / 2)
      (a ^ 2 * (2 * r) / (2 * s) / 2) r := by
    simpa using (hsd.const_add 1).div_const 2
  have e1 := (Real.hasDerivAt_binEntropy (p := (1 + b * r) / 2) (by intro h; linarith)
    (by intro h; linarith)).comp r hq1
  have e2 := (Real.hasDerivAt_binEntropy (p := (1 + s) / 2) (by intro h; linarith)
    (by intro h; linarith)).comp r hq2
  have hfun : (fun r => QAlgorithms.binEntropy2 ((1 + b * r) / 2) -
        QAlgorithms.binEntropy2 ((1 + √(1 - a ^ 2 + a ^ 2 * r ^ 2)) / 2)) =
      fun r => (Real.binEntropy ((1 + b * r) / 2) -
        Real.binEntropy ((1 + √(1 - a ^ 2 + a ^ 2 * r ^ 2)) / 2)) / Real.log 2 := by
    funext r; simp only [QAlgorithms.binEntropy2, sub_div]
  rw [hfun]
  refine ((e1.sub e2).div_const (Real.log 2)).congr_deriv ?_
  congr 1
  rw [G_J ha ha1 hb0 hb hr0.le hr1, ← hs, J, J, J_closed s hs0 hs1, J_closed (b * r) hbr0 hbr1]
  have l1 : 1 - (1 + b * r) / 2 = (1 - b * r) / 2 := by ring
  have l2 : 1 - (1 + s) / 2 = (1 - s) / 2 := by ring
  rw [l1, l2, log_half _ (by linarith), log_half _ (by linarith), log_half _ (by linarith),
    log_half _ (by linarith)]
  field_simp
  ring

lemma G_zero (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    G a b 0 = a ^ 2 * QAlgorithms.Papers.Independent.Information100.P08.tanhRatio
      (√(1 - a ^ 2)) - b ^ 2 := by
  have ha1 : a < 1 := by linarith
  have hb0 : 0 < b := by linarith
  obtain ⟨hs0, hs1, -⟩ := s_facts ha ha1 le_rfl one_pos
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero] at hs0 hs1
  rw [G_J ha ha1 hb0 hb le_rfl one_pos]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, J_zero,
    mul_one]
  congr 2
  unfold QAlgorithms.Papers.Independent.Information100.P08.tanhRatio
    QAlgorithms.Papers.Independent.Information100.P08.inverseTanh
  rw [if_neg hs0.ne', J, J_closed _ hs0 hs1, Real.log_div (by linarith) (by linarith)]
  ring

/-- the full abstract statement -/
lemma main (ha : 0 < a) (hab : a < b) (hb : b < 1)
    (f : ℝ → ℝ) (hf : f = fun r => QAlgorithms.binEntropy2 ((1 + b * r) / 2) -
        QAlgorithms.binEntropy2 ((1 + √(1 - a ^ 2 + a ^ 2 * r ^ 2)) / 2)) :
    (0 ≤ G a b 0 → ∀ r ∈ Set.Icc (0 : ℝ) 1, f 0 ≤ f r) ∧
    (G a b 0 < 0 → ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      deriv f r = 0 ∧
      (∀ z ∈ Set.Ioo (0 : ℝ) 1, deriv f z = 0 ↔ z = r) ∧
      StrictAntiOn f (Set.Icc 0 r) ∧
      StrictMonoOn f (Set.Icc r 1)) := by
  have ha1 : a < 1 := by linarith
  have hb0 : 0 < b := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hd : ∀ z ∈ Set.Ioo (0:ℝ) 1, deriv f z = z * G a b z / Real.log 2 := by
    intro z ⟨h0, h1⟩
    rw [hf]; exact (F_deriv ha hab hb h0 h1).deriv
  have hcont : ContinuousOn f (Set.Icc 0 1) := by
    rw [hf]
    apply Continuous.continuousOn
    unfold QAlgorithms.binEntropy2
    fun_prop
  have hneg : ∀ z ∈ Set.Ioo (0:ℝ) 1, G a b z < 0 → deriv f z < 0 := by
    intro z hz hG
    rw [hd z hz]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hz.1 hG) hl2
  have hpos : ∀ z ∈ Set.Ioo (0:ℝ) 1, 0 < G a b z → 0 < deriv f z := by
    intro z hz hG
    rw [hd z hz]
    exact div_pos (mul_pos hz.1 hG) hl2
  constructor
  · intro hG0 r hr
    have hmono : StrictMonoOn f (Set.Icc 0 1) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 1) hcont
      intro z hz
      rw [interior_Icc] at hz
      exact hpos z hz (key ha hab hb le_rfl hz.1 hz.2 hG0)
    exact hmono.monotoneOn ⟨le_rfl, zero_le_one⟩ hr hr.1
  · intro hG0
    obtain ⟨r2, h20, h21, hG2⟩ := exists_pos ha hab hb
    have hc := G_contOn ha ha1 hb0 hb h20.le h21
    obtain ⟨r, ⟨hr0, hr2⟩, hGr⟩ := intermediate_value_Icc h20.le hc ⟨hG0.le, hG2.le⟩
    have hr0' : 0 < r := by
      rcases hr0.lt_or_eq with h | h
      · exact h
      · subst h; linarith
    have hr1 : r < 1 := by linarith
    have hlt : ∀ z ∈ Set.Ioo (0:ℝ) 1, z < r → G a b z < 0 := by
      intro z hz hzr
      by_contra h
      push Not at h
      have := key ha hab hb hz.1.le hzr hr1 h
      linarith
    have hgt : ∀ z ∈ Set.Ioo (0:ℝ) 1, r < z → 0 < G a b z := by
      intro z hz hzr
      exact key ha hab hb hr0 hzr hz.2 hGr.ge
    refine ⟨r, ⟨hr0', hr1⟩, ?_, ?_, ?_, ?_⟩
    · rw [hd r ⟨hr0', hr1⟩, hGr]; simp
    · intro z hz
      constructor
      · intro h
        rcases lt_trichotomy z r with h' | h' | h'
        · linarith [hneg z hz (hlt z hz h')]
        · exact h'
        · linarith [hpos z hz (hgt z hz h')]
      · rintro rfl; rw [hd z hz, hGr]; simp
    · apply strictAntiOn_of_deriv_neg (convex_Icc 0 r) (hcont.mono (Set.Icc_subset_Icc le_rfl hr1.le))
      intro z hz
      rw [interior_Icc] at hz
      have hz' : z ∈ Set.Ioo (0:ℝ) 1 := ⟨hz.1, by linarith [hz.2]⟩
      exact hneg z hz' (hlt z hz' hz.2)
    · apply strictMonoOn_of_deriv_pos (convex_Icc r 1) (hcont.mono (Set.Icc_subset_Icc hr0 le_rfl))
      intro z hz
      rw [interior_Icc] at hz
      have hz' : z ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hz.1], hz.2⟩
      exact hpos z hz' (hgt z hz' hz.1)

end

end S202GD

open QAlgorithms.Papers.Independent.Information100.P08 in
theorem solution (p : ℝ) (hp : 0 < p) (hpUpper : p < 2 / 3) :
    (0 ≤ optimizerSign p → ∀ r ∈ Set.Icc (0 : ℝ) 1, optimizerPenalty p 0 ≤ optimizerPenalty p r) ∧
    (optimizerSign p < 0 → ∃ r ∈ Set.Ioo (0 : ℝ) 1,
      deriv (optimizerPenalty p) r = 0 ∧
      (∀ z ∈ Set.Ioo (0 : ℝ) 1, deriv (optimizerPenalty p) z = 0 ↔ z = r) ∧
      StrictAntiOn (optimizerPenalty p) (Set.Icc 0 r) ∧
      StrictMonoOn (optimizerPenalty p) (Set.Icc r 1)) := by
  have ha : 0 < 1 - 3 * p / 2 := by linarith
  have hab : 1 - 3 * p / 2 < 1 - p := by linarith
  have hb : 1 - p < 1 := by linarith
  have hsign : optimizerSign p = S202GD.G (1 - 3 * p / 2) (1 - p) 0 := by
    rw [S202GD.G_zero ha hab hb]; rfl
  rw [hsign]
  exact S202GD.main ha hab hb (optimizerPenalty p) rfl
