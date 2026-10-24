-- Prove2me | solution 1 for SampleDrivenOS.Limit.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:24:03.482529+00:00
-- url     : https://prove2.me/submissions/ae450857-cd10-4f62-b354-519a17e1b285

import Mathlib
import Definitions.Def_SampleDrivenOS_Limit_Setting

open MeasureTheory Filter Topology Set

namespace L5Aux

open SampleDrivenOS.Limit SampleDrivenOS.Structure

section generic

variable {p : ℝ} {t : ℕ → ℝ}

lemma uniq (hmono : Monotone t) {τ : ℝ} {i j : ℕ} (hi1 : t i ≤ τ) (hi2 : τ < t (i + 1))
    (hj1 : t j ≤ τ) (hj2 : τ < t (j + 1)) : i = j := by
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := hmono (show i + 1 ≤ j by omega); linarith
  · have := hmono (show j + 1 ≤ i by omega); linarith

lemma tq_eq (hmono : Monotone t) {τ : ℝ} {i : ℕ} (hi1 : t i ≤ τ) (hi2 : τ < t (i + 1)) (ℓ : ℕ) :
    thresholdQ t τ ℓ = if ℓ ≤ i then thresholdProd t i / τ ^ (i + 1) else 0 := by
  have hex : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1) := ⟨i, hi1, hi2⟩
  unfold thresholdQ
  rw [dif_pos hex]
  have hf : Nat.find hex = i := uniq hmono (Nat.find_spec hex).1 (Nat.find_spec hex).2 hi1 hi2
  rw [hf]

lemma tq_none {τ : ℝ} (h : ¬ ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)) (ℓ : ℕ) :
    thresholdQ t τ ℓ = 0 := by
  unfold thresholdQ
  rw [dif_neg h]

lemma T_pos (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (i : ℕ) : 0 < thresholdProd t i := by
  unfold thresholdProd
  apply Finset.prod_pos
  intro j _
  exact lt_of_lt_of_le hp0 (hge j)

lemma T_le (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (i : ℕ) :
    thresholdProd t i ≤ t i ^ i := by
  unfold thresholdProd
  calc ∏ j ∈ Finset.Icc 1 i, t j ≤ ∏ _j ∈ Finset.Icc 1 i, t i :=
        Finset.prod_le_prod (fun j _ => le_trans hp0.le (hge j))
          (fun j hj => hmono (Finset.mem_Icc.1 hj).2)
    _ = t i ^ i := by simp [Finset.prod_const]

lemma T_succ (i : ℕ) : thresholdProd t (i + 1) = thresholdProd t i * t (i + 1) := by
  unfold thresholdProd
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma no_zero (ht0 : t 0 = p) (ht1 : t 1 = p) {τ : ℝ} (h1 : t 0 ≤ τ) (h2 : τ < t (0 + 1)) : False := by
  simp only [zero_add] at h2
  rw [ht0] at h1; rw [ht1] at h2; linarith

lemma tq_nonneg (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (τ : ℝ) (ℓ : ℕ) :
    0 ≤ thresholdQ t τ ℓ := by
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2]
    split_ifs
    · have := T_pos hp0 hge i
      have : 0 < τ := lt_of_lt_of_le hp0 (le_trans (hge i) hi1)
      positivity
    · exact le_rfl
  · rw [tq_none h]

lemma tq_le (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (τ : ℝ) (ℓ : ℕ) : thresholdQ t τ ℓ ≤ 1 / p := by
  have hp' : 0 ≤ 1 / p := by positivity
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2]
    split_ifs
    · have hT := T_le hp0 hge hmono i
      have hTp := T_pos hp0 hge i
      have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
      have hτ : 0 < τ := lt_of_lt_of_le hti hi1
      calc thresholdProd t i / τ ^ (i + 1) ≤ t i ^ i / t i ^ (i + 1) := by
            apply div_le_div₀ (by positivity) hT (by positivity)
            exact pow_le_pow_left₀ hti.le hi1 _
        _ = 1 / t i := by rw [pow_succ]; field_simp
        _ ≤ 1 / p := one_div_le_one_div_of_le hp0 (hge i)
    · exact hp'
  · rw [tq_none h]; exact hp'

lemma tq_anti (hmono : Monotone t) (τ : ℝ) {ℓ j : ℕ} (hℓj : ℓ ≤ j)
    (hnn : ∀ i, 0 ≤ thresholdProd t i / τ ^ (i + 1)) :
    thresholdQ t τ j ≤ thresholdQ t τ ℓ := by
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    rw [tq_eq hmono hi1 hi2, tq_eq hmono hi1 hi2]
    split_ifs with h1 h2 <;> first | exact le_rfl | (exfalso; omega) | exact hnn i
  · rw [tq_none h, tq_none h]

lemma tq_measurable (hmono : Monotone t) (ℓ : ℕ) : Measurable (fun τ => thresholdQ t τ ℓ) := by
  set f : ℕ → ℝ → ℝ := fun n τ => ∑ i ∈ Finset.range n,
    (Ico (t i) (t (i + 1))).indicator
      (fun τ => if ℓ ≤ i then thresholdProd t i / τ ^ (i + 1) else 0) τ
  have hf : ∀ n, Measurable (f n) := by
    intro n
    apply Finset.measurable_sum
    intro i _
    apply Measurable.indicator _ measurableSet_Ico
    split_ifs
    · exact measurable_const.div (measurable_id.pow_const _)
    · exact measurable_const
  apply measurable_of_tendsto_metrizable hf
  rw [tendsto_pi_nhds]
  intro τ
  apply tendsto_nhds_of_eventually_eq
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · obtain ⟨i, hi1, hi2⟩ := h
    filter_upwards [eventually_gt_atTop i] with n hn
    simp only [f]
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hn)]
    · rw [indicator_of_mem (show τ ∈ Ico (t i) (t (i + 1)) from ⟨hi1, hi2⟩), tq_eq hmono hi1 hi2]
    · intro j _ hji
      rw [indicator_of_notMem]
      rintro ⟨hj1, hj2⟩
      exact hji (uniq hmono hj1 hj2 hi1 hi2)
  · apply Eventually.of_forall
    intro n
    simp only [f]
    rw [tq_none h]
    apply Finset.sum_eq_zero
    intro i _
    rw [indicator_of_notMem]
    rintro ⟨hj1, hj2⟩
    exact h ⟨i, hj1, hj2⟩

lemma tq_integrableOn (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (ℓ : ℕ) (a b : ℝ) : IntegrableOn (fun τ => thresholdQ t τ ℓ) (Icc a b) := by
  apply IntegrableOn.of_bound (by simp) (tq_measurable hmono ℓ).aestronglyMeasurable (1 / p)
  apply Eventually.of_forall
  intro τ
  rw [Real.norm_eq_abs, abs_of_nonneg (tq_nonneg hp0 hge hmono τ ℓ)]
  exact tq_le hp0 hge hmono ht0 ht1 τ ℓ

/-- the integrand of `cumMass` -/
lemma hasDeriv_Tpow (T : ℝ) (i : ℕ) (hi : 1 ≤ i) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => -(T / x ^ i)) ((i : ℝ) * (T / x ^ (i + 1))) x := by
  have h := ((hasDerivAt_pow i x).inv (pow_ne_zero i hx.ne')).const_mul T
  have h2 := h.neg
  refine (h2.congr_deriv ?_).congr_of_eventuallyEq ?_
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring
  · apply Eventually.of_forall; intro y; simp [div_eq_mul_inv]

lemma tq_x_intervalIntegrable (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t)
    (ht0 : t 0 = p) (ht1 : t 1 = p) (j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun x => x * thresholdQ t x j) volume a b := by
  apply IntegrableOn.intervalIntegrable
  rw [uIcc_eq_union]
  apply IntegrableOn.union
  · exact IntegrableOn.continuousOn_mul continuousOn_id
      (tq_integrableOn hp0 hge hmono ht0 ht1 j _ _) isCompact_Icc
  · exact IntegrableOn.continuousOn_mul continuousOn_id
      (tq_integrableOn hp0 hge hmono ht0 ht1 j _ _) isCompact_Icc

lemma piece (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (i j : ℕ) :
    ∫ x in t i..t (i + 1), x * thresholdQ t x j =
      if j ≤ i then ∫ x in t i..t (i + 1), thresholdProd t i / x ^ i else 0 := by
  have hle : t i ≤ t (i + 1) := hmono (Nat.le_succ i)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ ({t (i + 1)} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton)
  have key : ∫ x in t i..t (i + 1), x * thresholdQ t x j =
      ∫ x in t i..t (i + 1), (if j ≤ i then thresholdProd t i / x ^ i else 0) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hne] with x hx hxI
    rw [uIoc_of_le hle] at hxI
    have hxb : x < t (i + 1) := lt_of_le_of_ne hxI.2 (by simpa using hx)
    rw [tq_eq hmono hxI.1.le hxb]
    have hx0 : 0 < x := lt_of_lt_of_le hp0 (le_trans (hge i) hxI.1.le)
    split_ifs
    · rw [pow_succ]; field_simp
    · ring
  rw [key]
  split_ifs
  · rfl
  · simp

lemma partial_int (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (j n : ℕ) :
    ∫ x in p..t n, x * thresholdQ t x j =
      ∑ i ∈ Finset.range n, ∫ x in t i..t (i + 1), x * thresholdQ t x j := by
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := t)
    (fun k _ => tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j _ _), ht0]

/-- `a_i = T_i / t_i^{i-1}` -/
noncomputable def aa (t : ℕ → ℝ) (i : ℕ) : ℝ := thresholdProd t i / t i ^ (i - 1)

lemma aa_bounds (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (hle1 : ∀ i, t i ≤ 1)
    (i : ℕ) (hi : 1 ≤ i) : 0 ≤ aa t i ∧ aa t i ≤ 1 := by
  have hti : 0 < t i := lt_of_lt_of_le hp0 (hge i)
  have hT := T_pos hp0 hge i
  have hTle := T_le hp0 hge hmono i
  unfold aa
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    calc thresholdProd t (j + 1) ≤ t (j + 1) ^ (j + 1) := hTle
      _ = t (j + 1) ^ j * t (j + 1) := pow_succ _ _
      _ ≤ t (j + 1) ^ j * 1 := mul_le_mul_of_nonneg_left (hle1 _) (by positivity)
      _ = t (j + 1) ^ j := mul_one _

lemma piece_gen (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (m : ℕ) :
    ∫ x in t (m + 2)..t (m + 2 + 1), thresholdProd t (m + 2) / x ^ (m + 2) =
      (aa t (m + 2) - aa t (m + 3)) / ((m : ℝ) + 1) := by
  set T := thresholdProd t (m + 2)
  have hmono_i : t (m + 2) ≤ t (m + 2 + 1) := hmono (Nat.le_succ _)
  have hti : 0 < t (m + 2) := lt_of_lt_of_le hp0 (hge _)
  have hti1 : 0 < t (m + 3) := lt_of_lt_of_le hp0 (hge _)
  have hint : ∫ x in t (m + 2)..t (m + 2 + 1), T / x ^ (m + 2) =
      (1 / ((m : ℝ) + 1)) * (T / t (m + 2) ^ (m + 1) - T / t (m + 3) ^ (m + 1)) := by
    have hfun : (fun x : ℝ => T / x ^ (m + 2)) =
        fun x => (1 / ((m : ℝ) + 1)) * (((m + 1 : ℕ) : ℝ) * (T / x ^ (m + 1 + 1))) := by
      funext x; push_cast; field_simp
    rw [hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -(T / x ^ (m + 1)))]
    · ring
    · intro x hx
      rw [uIcc_of_le hmono_i] at hx
      exact hasDeriv_Tpow T (m + 1) (by omega) x (lt_of_lt_of_le hti hx.1)
    · apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.div continuousOn_const (continuousOn_pow _)
      intro x hx
      rw [uIcc_of_le hmono_i] at hx
      exact pow_ne_zero _ (lt_of_lt_of_le hti hx.1).ne'
  rw [hint]
  unfold aa
  rw [T_succ (m + 2)]
  simp only [show m + 2 - 1 = m + 1 by omega, show m + 3 - 1 = m + 2 by omega]
  have h3 : t (m + 2 + 1) = t (m + 3) := rfl
  rw [h3, pow_succ (t (m + 3)) (m + 1)]
  field_simp
  ring

lemma piece_one (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht1 : t 1 = p) :
    ∫ x in t 1..t (1 + 1), thresholdProd t 1 / x ^ 1 = p * Real.log (t 2 / p) := by
  have hT : thresholdProd t 1 = p := by unfold thresholdProd; simp [ht1]
  rw [hT, ht1]
  simp only [pow_one]
  rw [show (fun x : ℝ => p / x) = fun x => p * (1 / x) by funext x; ring,
    intervalIntegral.integral_const_mul, integral_one_div_of_pos hp0
      (lt_of_lt_of_le hp0 (hge _))]

/-- partial sums of the pieces, `j = k ≥ 2` -/
lemma partial_closed (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (k : ℕ) (hk : 2 ≤ k) (m : ℕ) :
    ∫ x in p..t (k + 1 + m), x * thresholdQ t x k =
      aa t k / ((k : ℝ) - 1) -
        ∑ i ∈ Finset.range m, aa t (i + (k + 1)) / ((((i + (k + 1) : ℕ) : ℝ) - 2) *
          (((i + (k + 1) : ℕ) : ℝ) - 1)) - aa t (k + 1 + m) / ((k : ℝ) + m - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c, k = c + 2 := ⟨k - 2, by omega⟩
  rw [partial_int hp0 hge hmono ht0 ht1]
  induction m with
  | zero =>
    rw [show c + 2 + 1 + 0 = (c + 2) + 1 by omega, Finset.sum_range_succ]
    rw [Finset.sum_eq_zero (fun i hi => by
      rw [piece hp0 hge hmono, if_neg (by simp at hi; omega)])]
    rw [piece hp0 hge hmono, if_pos le_rfl, piece_gen hp0 hge hmono c]
    push_cast
    simp only [Finset.range_zero, Finset.sum_empty]
    have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
    have e1 : (c : ℝ) + 1 ≠ 0 := by linarith
    have e2 : (c : ℝ) + 2 - 1 ≠ 0 := by linarith
    have e3 : (c : ℝ) + 2 + 0 - 1 ≠ 0 := by linarith
    field_simp
    ring
  | succ m ih =>
    rw [show c + 2 + 1 + (m + 1) = (c + 2 + 1 + m) + 1 by omega, Finset.sum_range_succ, ih,
      piece hp0 hge hmono, if_pos (by omega),
      show c + 2 + 1 + m = (c + 1 + m) + 2 by omega, piece_gen hp0 hge hmono (c + 1 + m),
      Finset.sum_range_succ]
    rw [show c + 1 + m + 3 = (c + 1 + m + 2) + 1 by omega,
      show m + (c + 2 + 1) = c + 1 + m + 2 by omega]
    push_cast
    have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have h1 : (c : ℝ) + 1 + m + 1 ≠ 0 := by linarith
    have h2 : (c : ℝ) + 2 + m - 1 ≠ 0 := by linarith
    have h3 : (c : ℝ) + 2 + ((m : ℝ) + 1) - 1 ≠ 0 := by linarith
    have h5 : (c : ℝ) + 2 - 1 ≠ 0 := by linarith
    have h6 : (c : ℝ) + 1 + m + 2 - 2 ≠ 0 := by linarith
    have h7 : (c : ℝ) + 1 + m + 2 - 1 ≠ 0 := by linarith
    field_simp
    ring

end generic


section limits

variable {p : ℝ} {t : ℕ → ℝ}

lemma I_lim (hp0 : 0 < p) (hp1 : p < 1) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (ht0 : t 0 = p)
    (ht1 : t 1 = p) (hle1 : ∀ i, t i ≤ 1) (j : ℕ) :
    Tendsto (fun n => ∫ x in p..t n, x * thresholdQ t x j) atTop
      (𝓝 (∫ x in p..1, x * thresholdQ t x j)) := by
  have hbdd : BddAbove (Set.range t) := ⟨1, by rintro _ ⟨n, rfl⟩; exact hle1 n⟩
  set L := ⨆ n, t n
  have hL : Tendsto t atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have hLge : ∀ n, t n ≤ L := fun n => le_ciSup hbdd n
  have hLle : L ≤ 1 := ciSup_le hle1
  have hpL : p ≤ L := le_trans (hge 0) (hLge 0)
  -- the integral over [L, 1] vanishes
  have hzero : ∫ x in L..1, x * thresholdQ t x j = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro x hx
      rw [uIcc_of_le hLle] at hx
      simp only
      rw [tq_none, mul_zero]
      rintro ⟨i, _, hi2⟩
      have := hLge (i + 1)
      linarith [hx.1]
  have hsplit : ∫ x in p..1, x * thresholdQ t x j = ∫ x in p..L, x * thresholdQ t x j := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j p L)
      (tq_x_intervalIntegrable hp0 hge hmono ht0 ht1 j L 1), hzero, add_zero]
  rw [hsplit]
  have hcont := intervalIntegral.continuousOn_primitive_interval (μ := volume)
    (f := fun x => x * thresholdQ t x j) (a := p) (b := 1)
    (by
      rw [uIcc_of_le hp1.le]
      exact IntegrableOn.continuousOn_mul continuousOn_id
        (tq_integrableOn hp0 hge hmono ht0 ht1 j p 1) isCompact_Icc)
  have hLmem : L ∈ uIcc p 1 := by rw [uIcc_of_le hp1.le]; exact ⟨hpL, hLle⟩
  have hcw := (hcont L hLmem).tendsto
  apply hcw.comp
  apply tendsto_nhdsWithin_iff.2 ⟨hL, Eventually.of_forall (fun n => ?_)⟩
  rw [uIcc_of_le hp1.le]
  exact ⟨hge n, hle1 n⟩

lemma summable_g (hp0 : 0 < p) (hge : ∀ i, p ≤ t i) (hmono : Monotone t) (hle1 : ∀ i, t i ≤ 1)
    (k : ℕ) (hk : 2 ≤ k) :
    Summable (fun i : ℕ => aa t (i + (k + 1)) / ((((i + (k + 1) : ℕ) : ℝ) - 2) *
      (((i + (k + 1) : ℕ) : ℝ) - 1))) := by
  have h2 : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ 2) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
    simpa using this
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) h2
  · obtain ⟨h0, -⟩ := aa_bounds hp0 hge hmono hle1 (i + (k + 1)) (by omega)
    push_cast
    have : (0:ℝ) < ((i : ℝ) + (k + 1) - 2) * ((i : ℝ) + (k + 1) - 1) := by
      have : (2:ℝ) ≤ k := by exact_mod_cast hk
      have : (0:ℝ) ≤ i := Nat.cast_nonneg i
      apply mul_pos <;> linarith
    positivity
  · obtain ⟨h0, h1⟩ := aa_bounds hp0 hge hmono hle1 (i + (k + 1)) (by omega)
    push_cast
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
    have hpos : (0:ℝ) < ((i : ℝ) + (k + 1) - 2) * ((i : ℝ) + (k + 1) - 1) := by
      apply mul_pos <;> linarith
    calc aa t (i + (k + 1)) / (((i : ℝ) + (k + 1) - 2) * ((i : ℝ) + (k + 1) - 1))
        ≤ 1 / (((i : ℝ) + (k + 1) - 2) * ((i : ℝ) + (k + 1) - 1)) :=
          div_le_div_of_nonneg_right h1 hpos.le
      _ ≤ 1 / ((i : ℝ) + 1) ^ 2 := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith

lemma mu_eq (k : ℕ) :
    mu t (k + 1) = ∑' i : ℕ, aa t (i + (k + 1)) / ((((i + (k + 1) : ℕ) : ℝ) - 2) *
      (((i + (k + 1) : ℕ) : ℝ) - 1)) := by
  unfold mu aa
  congr 1
  funext i
  ring

lemma Ik_val (hp0 : 0 < p) (hp1 : p < 1) (hge : ∀ i, p ≤ t i) (hmono : Monotone t)
    (ht0 : t 0 = p) (ht1 : t 1 = p) (hle1 : ∀ i, t i ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    ∫ x in p..1, x * thresholdQ t x k = aa t k / ((k : ℝ) - 1) - mu t (k + 1) := by
  have h1 := (I_lim hp0 hp1 hge hmono ht0 ht1 hle1 k).comp
    (tendsto_add_atTop_nat (k + 1))
  have hsum := (summable_g hp0 hge hmono hle1 k hk).hasSum.tendsto_sum_nat
  have hbd : Tendsto (fun m : ℕ => aa t (k + 1 + m) / ((k : ℝ) + m - 1)) atTop (𝓝 0) := by
    have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
    apply squeeze_zero (fun m => ?_) (fun m => ?_) (g := fun m : ℕ => 1 / ((m : ℝ) + 1))
      tendsto_one_div_add_atTop_nhds_zero_nat
    · obtain ⟨h0, -⟩ := aa_bounds hp0 hge hmono hle1 (k + 1 + m) (by omega)
      have : (0:ℝ) < (k : ℝ) + m - 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
      positivity
    · obtain ⟨h0, h1⟩ := aa_bounds hp0 hge hmono hle1 (k + 1 + m) (by omega)
      have hm0 := Nat.cast_nonneg (α := ℝ) m
      have hpos : (0:ℝ) < (k : ℝ) + m - 1 := by linarith
      calc aa t (k + 1 + m) / ((k : ℝ) + m - 1) ≤ 1 / ((k : ℝ) + m - 1) :=
            div_le_div_of_nonneg_right h1 hpos.le
        _ ≤ 1 / ((m : ℝ) + 1) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have h2 : Tendsto (fun m : ℕ => ∫ x in p..t (k + 1 + m), x * thresholdQ t x k) atTop
      (𝓝 (aa t k / ((k : ℝ) - 1) - mu t (k + 1) - 0)) := by
    rw [mu_eq]
    have := ((tendsto_const_nhds (x := aa t k / ((k : ℝ) - 1))).sub hsum).sub hbd
    refine this.congr (fun m => ?_)
    rw [partial_closed hp0 hge hmono ht0 ht1 k hk m]
  rw [sub_zero] at h2
  refine tendsto_nhds_unique ?_ h2
  refine h1.congr (fun m => ?_)
  simp only [Function.comp, show m + (k + 1) = k + 1 + m by omega]

lemma I1_val (hp0 : 0 < p) (hp1 : p < 1) (hge : ∀ i, p ≤ t i) (hmono : Monotone t)
    (ht0 : t 0 = p) (ht1 : t 1 = p) (hle1 : ∀ i, t i ≤ 1) :
    ∫ x in p..1, x * thresholdQ t x 1 = p * Real.log (t 2 / p) + p - mu t 3 := by
  have h2 := Ik_val hp0 hp1 hge hmono ht0 ht1 hle1 2 le_rfl
  have ha2 : aa t 2 = p := by
    unfold aa thresholdProd
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), ht1]
    have : 0 < t 2 := lt_of_lt_of_le hp0 (hge 2)
    simp only [show 2 - 1 = 1 by rfl, pow_one]
    field_simp
  rw [ha2] at h2
  norm_num at h2
  -- difference of the partial integrals is the first piece
  have hdiff : ∀ m : ℕ, ∫ x in p..t (m + 2), x * thresholdQ t x 1 =
      (∫ x in p..t (m + 2), x * thresholdQ t x 2) + p * Real.log (t 2 / p) := by
    intro m
    rw [partial_int hp0 hge hmono ht0 ht1, partial_int hp0 hge hmono ht0 ht1,
      ← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem 1 (Finset.mem_range.2 (by omega))]
    · rw [piece hp0 hge hmono, piece hp0 hge hmono, if_pos le_rfl, if_neg (by norm_num),
        sub_zero, piece_one hp0 hge hmono ht1]
    · intro i _ hi
      rw [piece hp0 hge hmono, piece hp0 hge hmono]
      rcases Nat.lt_or_ge i 2 with h | h
      · have : i = 0 := by omega
        subst this
        simp
      · rw [if_pos (by omega), if_pos h, sub_self]
  have hA := (I_lim hp0 hp1 hge hmono ht0 ht1 hle1 1).comp (tendsto_add_atTop_nat 2)
  have hB := ((I_lim hp0 hp1 hge hmono ht0 ht1 hle1 2).comp (tendsto_add_atTop_nat 2)).add_const
    (p * Real.log (t 2 / p))
  have hA' : Tendsto (fun m : ℕ => ∫ x in p..t (m + 2), x * thresholdQ t x 1) atTop
      (𝓝 ((∫ x in p..1, x * thresholdQ t x 2) + p * Real.log (t 2 / p))) :=
    hB.congr (fun m => (hdiff m).symm)
  have := tendsto_nhds_unique hA hA'
  rw [this, h2]
  ring

end limits

/-- modify index `0` to `p` -/
noncomputable def tmod (p : ℝ) (t : ℕ → ℝ) : ℕ → ℝ := fun i => if i = 0 then p else t i

lemma thresholdProd_tmod (p : ℝ) (t : ℕ → ℝ) (n : ℕ) :
    thresholdProd (tmod p t) n = thresholdProd t n := by
  unfold thresholdProd tmod
  apply Finset.prod_congr rfl
  intro i hi
  rw [if_neg (by simp at hi; omega)]

lemma tq_tmod (p : ℝ) (t : ℕ → ℝ) (ht1 : t 1 = p) {τ : ℝ} (hτ : p ≤ τ) (j : ℕ) :
    thresholdQ t τ j = thresholdQ (tmod p t) τ j := by
  have hiff : ∀ i, (t i ≤ τ ∧ τ < t (i + 1)) ↔ (tmod p t i ≤ τ ∧ τ < tmod p t (i + 1)) := by
    intro i
    unfold tmod
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h
      simp only [if_true, zero_add, one_ne_zero, if_false, ht1]
      constructor
      · rintro ⟨_, h2⟩; linarith
      · rintro ⟨_, h2⟩; linarith
    · rw [if_neg (by omega), if_neg (by omega)]
  unfold thresholdQ
  by_cases h : ∃ i : ℕ, t i ≤ τ ∧ τ < t (i + 1)
  · have h' : ∃ i : ℕ, tmod p t i ≤ τ ∧ τ < tmod p t (i + 1) := by
      obtain ⟨i, hi⟩ := h; exact ⟨i, (hiff i).1 hi⟩
    rw [dif_pos h, dif_pos h']
    have hf : Nat.find h = Nat.find h' :=
      le_antisymm (Nat.find_min' h ((hiff _).2 (Nat.find_spec h')))
        (Nat.find_min' h' ((hiff _).1 (Nat.find_spec h)))
    rw [hf, thresholdProd_tmod]
  · have h' : ¬ ∃ i : ℕ, tmod p t i ≤ τ ∧ τ < tmod p t (i + 1) := by
      rintro ⟨i, hi⟩; exact h ⟨i, (hiff i).2 hi⟩
    rw [dif_neg h, dif_neg h']

lemma mu_tmod (p : ℝ) (t : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) : mu (tmod p t) k = mu t k := by
  unfold mu
  congr 1
  funext i
  rw [thresholdProd_tmod]
  unfold tmod
  rw [if_neg (by omega)]

end L5Aux

open L5Aux SampleDrivenOS.Limit SampleDrivenOS.Structure in
theorem solution (p : ℝ) (hp : p ∈ Set.Ioo (0:ℝ) 1) (t : ℕ → ℝ) (ht1 : t 1 = p)
    (hmono : ∀ i : ℕ, 1 ≤ i → t i ≤ t (i + 1)) (hle : ∀ i : ℕ, 1 ≤ i → t i ≤ 1) (α : ℝ) :
    (∀ k : ℕ, 1 ≤ k →
        α = 1 / (1 - p ^ k) * ∑ j ∈ Finset.Icc 1 k, ∫ τ in p..1, τ * SampleDrivenOS.Limit.thresholdQ t τ j) ↔
      (α * (1 - p) = p * Real.log (t 2 / p) + p - SampleDrivenOS.Limit.mu t 3 ∧
        ∀ k : ℕ, 2 ≤ k → α * (1 - p) * p ^ (k - 1) =
          1 / ((k : ℝ) - 1) * (SampleDrivenOS.Structure.thresholdProd t k / t k ^ (k - 1)) -
            SampleDrivenOS.Limit.mu t (k + 1)) := by
  obtain ⟨hp0, hp1⟩ := hp
  set t' := tmod p t
  have ht'0 : t' 0 = p := by simp [t', tmod]
  have ht'1 : t' 1 = p := by simp [t', tmod, ht1]
  have ht'i : ∀ i, 1 ≤ i → t' i = t i := fun i hi => by simp [t', tmod]; omega
  have hmono' : Monotone t' := by
    apply monotone_nat_of_le_succ
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [ht'0, ht'1]
    · rw [ht'i n h, ht'i (n + 1) (by omega)]; exact hmono n h
  have hge' : ∀ i, p ≤ t' i := fun i => ht'0 ▸ hmono' (Nat.zero_le i)
  have hle' : ∀ i, t' i ≤ 1 := by
    intro i
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; rw [ht'0]; exact hp1.le
    · rw [ht'i i h]; exact hle i h
  -- the integrals
  set I : ℕ → ℝ := fun j => ∫ τ in p..1, τ * thresholdQ t τ j
  have hI : ∀ j, I j = ∫ τ in p..1, τ * thresholdQ t' τ j := by
    intro j
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hp1.le] at hx
    simp only
    rw [tq_tmod p t ht1 hx.1 j]
  have hI1 : I 1 = p * Real.log (t 2 / p) + p - mu t 3 := by
    rw [hI, I1_val hp0 hp1 hge' hmono' ht'0 ht'1 hle', ht'i 2 (by norm_num),
      mu_tmod p t 3 (by norm_num)]
  have hIk : ∀ k, 2 ≤ k → I k = 1 / ((k : ℝ) - 1) * (thresholdProd t k / t k ^ (k - 1)) -
      mu t (k + 1) := by
    intro k hk
    rw [hI, Ik_val hp0 hp1 hge' hmono' ht'0 ht'1 hle' k hk, mu_tmod p t (k + 1) (by omega)]
    unfold aa
    rw [thresholdProd_tmod, ht'i k (by omega)]
    ring
  have hpk : ∀ k : ℕ, 1 ≤ k → 1 - p ^ k ≠ 0 := by
    intro k hk
    have : p ^ k < 1 := pow_lt_one₀ hp0.le hp1 (by omega)
    linarith
  show (∀ k : ℕ, 1 ≤ k → α = 1 / (1 - p ^ k) * ∑ j ∈ Finset.Icc 1 k, I j) ↔ _
  rw [← hI1]
  constructor
  · intro h14
    have hS : ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 k, I j = α * (1 - p ^ k) := by
      intro k hk
      have := h14 k hk
      rw [this]
      field_simp [hpk k hk]
    refine ⟨?_, fun k hk => ?_⟩
    · have := hS 1 le_rfl
      simp only [Finset.Icc_self, Finset.sum_singleton, pow_one] at this
      linarith
    · rw [← hIk k hk]
      obtain ⟨c, rfl⟩ : ∃ c, k = c + 2 := ⟨k - 2, by omega⟩
      have h1 := hS (c + 2) (by omega)
      have h2 := hS (c + 1) (by omega)
      rw [show c + 2 = (c + 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega)] at h1
      rw [show c + 2 - 1 = c + 1 by omega]
      have e : α * (1 - p ^ (c + 1 + 1)) - α * (1 - p ^ (c + 1)) = α * (1 - p) * p ^ (c + 1) := by
        ring
      rw [show (c + 1 + 1) = c + 2 by omega] at h1 e
      linarith
  · rintro ⟨h15, h16⟩
    have hS : ∀ k, 1 ≤ k → ∑ j ∈ Finset.Icc 1 k, I j = α * (1 - p ^ k) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simp only [Finset.Icc_self, Finset.sum_singleton, pow_one]; linarith
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ih, hIk (n + 1) (by omega), ← h16 (n + 1) (by omega)]
        simp only [Nat.add_sub_cancel]
        ring
    intro k hk
    rw [hS k hk]
    field_simp [hpk k hk]
