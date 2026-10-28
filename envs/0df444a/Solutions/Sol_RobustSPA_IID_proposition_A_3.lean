-- Prove2me | solution 1 for RobustSPA.IID.proposition_A_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T17:22:19.134655+00:00
-- url     : https://prove2.me/submissions/5a6253ef-830f-49d8-87b7-8b23645128c6

import Mathlib
import Definitions.Def_RobustSPA_IID_Setting
import Definitions.Def_RobustSPA_Affiliated_Setting
import Theorems.Thm_RobustSPA_IID_proposition_A_3_phi
import Theorems.Thm_RobustSPA_Affiliated_regret_Fstar_eq

open MeasureTheory Set RobustSPA.IID
namespace RSPARoot

/-- derivative of `rEq` -/
lemma hasDerivAt_rEq (m : ℕ) (r : ℝ) (hr : 0 < r) :
    HasDerivAt (rEq (m + 1))
      (-(m : ℝ) * (1 - r) ^ (m - 1) + 1 / r - ∑ j ∈ Finset.range m, (1 - r) ^ j) r := by
  have h1 : HasDerivAt (fun r : ℝ => (1 - r) ^ m) ((m : ℝ) * (1 - r) ^ (m - 1) * (-1)) r := by
    have := ((hasDerivAt_id r).const_sub 1).fun_pow m
    simpa using this
  have h2 : HasDerivAt Real.log (1 / r) r := by
    simpa [one_div] using Real.hasDerivAt_log hr.ne'
  have h3 : HasDerivAt (fun r : ℝ => ∑ k ∈ Finset.Ico 1 (m + 1), (1 - r) ^ k / (k : ℝ))
      (∑ k ∈ Finset.Ico 1 (m + 1), (k : ℝ) * (1 - r) ^ (k - 1) * (-1) / (k : ℝ)) r := by
    apply HasDerivAt.fun_sum
    intro k _
    have := (((hasDerivAt_id r).const_sub 1).fun_pow k).div_const (k : ℝ)
    simpa using this
  have hsum : ∑ k ∈ Finset.Ico 1 (m + 1), (k : ℝ) * (1 - r) ^ (k - 1) * (-1) / (k : ℝ)
      = -∑ j ∈ Finset.range m, (1 - r) ^ j := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have : ((1 + j : ℕ) : ℝ) ≠ 0 := by positivity
    simp only [Nat.add_sub_cancel_left]
    field_simp
  have := (h1.fun_add h2).fun_add h3
  rw [hsum] at this
  have hf : rEq (m + 1) = fun r : ℝ => (1 - r) ^ m + Real.log r +
      ∑ k ∈ Finset.Ico 1 (m + 1), (1 - r) ^ k / (k : ℝ) := by
    funext x; simp [rEq]
  rw [hf]
  exact this.congr_deriv (by ring)

lemma deriv_formula (m : ℕ) (hm : 1 ≤ m) (r : ℝ) (hr : 0 < r) :
    -(m : ℝ) * (1 - r) ^ (m - 1) + 1 / r - ∑ j ∈ Finset.range m, (1 - r) ^ j
      = (1 - r) ^ (m - 1) * (1 - (m + 1) * r) / r := by
  have hg := geom_sum_mul (1 - r) m
  have e : (1 - r) ^ m = (1 - r) ^ (m - 1) * (1 - r) := by
    rw [← pow_succ]; congr 1; omega
  rw [e] at hg
  field_simp
  have : (∑ i ∈ Finset.range m, (1 - r) ^ i) * r = 1 - (1 - r) ^ (m - 1) * (1 - r) := by
    linarith [hg]
  linear_combination (-1 : ℝ) * this

lemma cont_rEq (n : ℕ) : ContinuousOn (rEq n) (Ioi 0) := by
  unfold rEq
  apply ContinuousOn.add
  · apply ContinuousOn.add
    · fun_prop
    · exact Real.continuousOn_log.mono (fun x hx => ne_of_gt hx)
  · fun_prop

lemma rEq_one (m : ℕ) (hm : 1 ≤ m) : rEq (m + 1) 1 = 0 := by
  unfold rEq
  simp only [sub_self, Real.log_one, add_zero, Nat.add_sub_cancel]
  rw [zero_pow (by omega), zero_add]
  apply Finset.sum_eq_zero
  intro k hk
  rw [Finset.mem_Ico] at hk
  rw [zero_pow (by omega), zero_div]

lemma rEq_le (m : ℕ) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    rEq (m + 1) r ≤ 1 + m + Real.log r := by
  unfold rEq
  simp only [Nat.add_sub_cancel]
  have h0 : 0 ≤ 1 - r := by linarith
  have h1 : 1 - r ≤ 1 := by linarith
  have a : (1 - r) ^ m ≤ 1 := pow_le_one₀ h0 h1
  have b : ∑ k ∈ Finset.Ico 1 (m + 1), (1 - r) ^ k / (k : ℝ) ≤ ∑ _k ∈ Finset.Ico 1 (m + 1), (1 : ℝ) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
    rw [div_le_one (by linarith)]
    exact (pow_le_one₀ h0 h1).trans hk1
  simp at b
  linarith

theorem root (n : ℕ) (hn : 0 < n) :
    ∃ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 ∧
      ∀ r' ∈ Set.Ioo (0 : ℝ) 1, rEq n r' = 0 → r' = r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hval : ∀ r, rEq (0 + 1) r = 1 + Real.log r := by
      intro r; simp [rEq]
    refine ⟨Real.exp (-1), ⟨Real.exp_pos _, ?_⟩, ?_, ?_⟩
    · norm_num
    · rw [hval, Real.log_exp]; ring
    · intro r' hr' h
      rw [hval] at h
      have : Real.log r' = -1 := by linarith
      rw [← this, Real.exp_log hr'.1]
  · have hm1 : 1 ≤ m := hm
    have hnR : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    set c : ℝ := 1 / ((m : ℝ) + 1) with hc
    have hc0 : 0 < c := by positivity
    have hc1 : c < 1 := by
      rw [hc, div_lt_one hnR]; have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
    have hcast : (1 : ℝ) / ((m + 1 : ℕ) : ℝ) = c := by rw [hc]; push_cast; ring
    rw [hcast]
    -- monotonicity on (0, c] and antitonicity on [c, 1]
    have hderiv : ∀ x, 0 < x → HasDerivAt (rEq (m + 1))
        ((1 - x) ^ (m - 1) * (1 - (m + 1) * x) / x) x := by
      intro x hx
      rw [← deriv_formula m hm1 x hx]
      exact hasDerivAt_rEq m x hx
    have hmono : StrictMonoOn (rEq (m + 1)) (Ioc 0 c) := by
      apply strictMonoOn_of_deriv_pos (convex_Ioc 0 c)
      · exact (cont_rEq _).mono (fun x hx => hx.1)
      · intro x hx
        rw [interior_Ioc] at hx
        rw [(hderiv x hx.1).deriv]
        have hx1 : x < 1 := lt_trans hx.2 hc1
        have : 0 < 1 - (m + 1) * x := by
          have := hx.2; rw [hc, lt_div_iff₀ hnR] at this; linarith
        have : 0 < (1 - x) ^ (m - 1) := pow_pos (by linarith) _
        have := hx.1
        positivity
    have hanti : StrictAntiOn (rEq (m + 1)) (Icc c 1) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc c 1)
      · exact (cont_rEq _).mono (fun x hx => lt_of_lt_of_le hc0 hx.1)
      · intro x hx
        rw [interior_Icc] at hx
        have hx0 : 0 < x := lt_trans hc0 hx.1
        rw [(hderiv x hx0).deriv]
        have h1 : 1 - (m + 1) * x < 0 := by
          have := hx.1; rw [hc, div_lt_iff₀ hnR] at this; linarith
        have h2 : 0 < (1 - x) ^ (m - 1) := pow_pos (by linarith [hx.2]) _
        exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2 h1) hx0
    have hpos : ∀ x ∈ Ico c 1, 0 < rEq (m + 1) x := by
      intro x hx
      rw [← rEq_one m hm1]
      exact hanti ⟨hx.1, hx.2.le⟩ ⟨hc1.le, le_rfl⟩ hx.2
    have hcpos : 0 < rEq (m + 1) c := hpos c ⟨le_rfl, hc1⟩
    -- a point where rEq is negative
    set a : ℝ := Real.exp (-((m : ℝ) + 2)) with ha
    have ha0 : 0 < a := Real.exp_pos _
    have hac : a < c := by
      rw [ha, hc, lt_div_iff₀ hnR]
      have h := Real.add_one_le_exp ((m : ℝ) + 2)
      have he : Real.exp (-((m : ℝ) + 2)) * Real.exp ((m : ℝ) + 2) = 1 := by
        rw [← Real.exp_add]; simp
      have hp := Real.exp_pos (-((m : ℝ) + 2))
      nlinarith
    have haneg : rEq (m + 1) a < 0 := by
      have := rEq_le m a ha0 (by linarith)
      rw [ha, Real.log_exp] at this
      rw [ha]; linarith
    obtain ⟨r, hr, hr0⟩ : ∃ r ∈ Icc a c, rEq (m + 1) r = 0 :=
      intermediate_value_Icc hac.le ((cont_rEq _).mono (fun x hx => lt_of_lt_of_le ha0 hx.1))
        ⟨haneg.le, hcpos.le⟩
    have hrc : r < c := lt_of_le_of_ne hr.2 (fun h => by rw [h] at hr0; linarith)
    refine ⟨r, ⟨lt_of_lt_of_le ha0 hr.1, hrc⟩, hr0, ?_⟩
    intro r' hr' h'
    by_cases hlt : r' < c
    · exact hmono.injOn ⟨hr'.1, hlt.le⟩ ⟨lt_of_lt_of_le ha0 hr.1, hr.2⟩ (h'.trans hr0.symm)
    · exfalso
      have := hpos r' ⟨not_lt.mp hlt, hr'.2⟩
      linarith

end RSPARoot

namespace RSPAVal

/-- Bounds `0 ≤ Φ*_n(v) ≤ (v - r)/(n r)` on `(r, 1]` from the series form of Proposition A-3. -/
lemma phi_bounds (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (v : ℝ) (hv : v ∈ Set.Ioc r 1) :
    0 ≤ PhiStar n r v ∧ PhiStar n r v ≤ (v - r) / (n * r) := by
  have hS := (proposition_A_3_phi n hn r hr hrEq).1 v hv
  have hr0 := hr.1
  have hv0 : 0 < v := lt_trans hr0 hv.1
  set x := (v - r) / v with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith [hv.1]) hv0.le
  have hx1 : x < 1 := by rw [hx, div_lt_one hv0]; linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · exact hS.nonneg fun j => by positivity
  · have hgeo : HasSum (fun j : ℕ => (x / n) * x ^ j) ((x / n) * (1 - x)⁻¹) :=
      (hasSum_geometric_of_lt_one hx0 hx1).mul_left _
    have hle := hasSum_le (fun j => ?_) hS hgeo
    · have h1x : 1 - x = r / v := by rw [hx]; field_simp; ring
      calc PhiStar n r v ≤ (x / n) * (1 - x)⁻¹ := hle
        _ = (v - r) / (n * r) := by rw [h1x, hx]; field_simp
    · have hjn : (n : ℝ) ≤ ((j + n : ℕ) : ℝ) := by push_cast; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      have hxj : 0 ≤ x ^ (j + 1) := pow_nonneg hx0 _
      calc 1 / ((j + n : ℕ) : ℝ) * x ^ (j + 1) ≤ 1 / (n : ℝ) * x ^ (j + 1) :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hnR hjn) hxj
        _ = (x / n) * x ^ j := by rw [pow_succ]; ring

/-- The common bound on the integrands. -/
lemma integrand_bound (n : ℕ) (hn : 0 < n) (r p z w Φ : ℝ) (hr0 : 0 < r) (hp : p ∈ Set.Ioc r 1)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (hw : w ∈ Set.Icc (0 : ℝ) 1) (hΦ0 : 0 ≤ Φ)
    (hΦ1 : Φ ≤ (p - r) / (n * r)) :
    |(((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ|
      ≤ 3 / r := by
  have hd : 0 < p - r := by linarith [hp.1]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  set q := Φ / (p - r) with hq
  have hq0 : 0 ≤ q := div_nonneg hΦ0 hd.le
  have hq1 : q * (n * r) ≤ 1 := by
    rw [hq, div_mul_eq_mul_div, div_le_one hd]
    rw [le_div_iff₀ (by positivity)] at hΦ1
    linarith
  have hΦ : Φ = q * (p - r) := by rw [hq]; field_simp
  have heq : (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z + (n : ℝ) * w) * Φ
      = q * (((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w) := by
    rw [hΦ]; field_simp
  rw [heq, abs_mul, abs_of_nonneg hq0]
  have hp1 := hp.2
  have hbr : |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w| ≤ 3 * n := by
    rw [abs_le]
    have hr1 : r ≤ 1 := by linarith [hp.1]
    have e1 : 0 ≤ ((n : ℝ) - 1) * r := mul_nonneg (by linarith) hr0.le
    have e2 : ((n : ℝ) - 1) * r ≤ n := by nlinarith
    have e3 : 0 ≤ ((n : ℝ) - 1) * p * z := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hz.1
    have e4 : ((n : ℝ) - 1) * p * z ≤ n := by
      have : ((n : ℝ) - 1) * p ≤ n := by nlinarith
      nlinarith [hz.2, hz.1]
    have e5 : 0 ≤ n * (p - r) * w := mul_nonneg (mul_nonneg (by linarith) hd.le) hw.1
    have e6 : n * (p - r) * w ≤ n := by
      have : (n : ℝ) * (p - r) ≤ n := by nlinarith
      nlinarith [hw.2, hw.1]
    constructor <;> nlinarith
  have hr' : q ≤ 1 / (n * r) := by rw [le_div_iff₀ (by positivity)]; linarith
  calc q * |((n : ℝ) - 1) * r - (p - r) - ((n : ℝ) - 1) * p * z + n * (p - r) * w|
      ≤ (1 / (n * r)) * (3 * n) := mul_le_mul hr' hbr (abs_nonneg _) (by positivity)
    _ = 3 / r := by field_simp

lemma toReal_mem_Icc {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (s : Set α) : (μ s).toReal ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨ENNReal.toReal_nonneg, by
    have := prob_le_one (μ := μ) (s := s)
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)⟩

/-- Integrability of the integrand `(c₁ - 1 - c₂ z(p) + n w(p)) Φ*(p)` on `[r, 1]`. -/
lemma integrand_ii (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t)
    (z w : ℝ → ℝ) (hzm : Measurable z) (hwm : Measurable w)
    (hz : ∀ p ∈ Set.Ioc r 1, z p ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ p ∈ Set.Ioc r 1, w p ∈ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun p => (((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z p +
        (n : ℝ) * w p) * PhiStar n r p) volume r 1 := by
  have hr1 : r ≤ 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hn)]; exact_mod_cast hn
    linarith [hr.2]
  have hPhi : PhiStar n r = fun t => cdfOf ρ t := funext fun t => (hρ t).symm
  have hPm : Measurable (PhiStar n r) := by
    rw [hPhi]
    apply Monotone.measurable
    intro a b hab
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    exact measure_mono (Set.Iic_subset_Iic.mpr hab)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hr1]
  apply Measure.integrableOn_of_bounded (M := 3 / r) (by simp)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun p hp => ?_
    rw [Real.norm_eq_abs]
    obtain ⟨h0, h1⟩ := phi_bounds n hn r hr hrEq p hp
    exact integrand_bound n hn r p (z p) (w p) _ hr.1 hp (hz p hp) (hw p hp) h0 h1


lemma value_eq (n : ℕ) (hn : 0 < n) (r : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) (1 / (n : ℝ)))
    (hrEq : rEq n r = 0) (ρ : ProbabilityMeasure ℝ) (hρ : ∀ t, cdfOf ρ t = PhiStar n r t) :
    r + ∫ p in r..1, (((n : ℝ) - 1) * r / (p - r) - 1 -
        ((n : ℝ) - 1) * p / (p - r) * (1 - r / p) ^ n + (n : ℝ) * (1 - r / p) ^ (n - 1)) *
          PhiStar n r p = value n r := by
  have hr0 := hr.1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : r < 1 := by
    have h1 : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hnR
    linarith [hr.2]
  have hx01 : ∀ p ∈ Set.Ioc r 1, ∀ k : ℕ, (1 - r / p) ^ k ∈ Set.Icc (0 : ℝ) 1 := by
    intro p hp k
    have hp0 : 0 < p := lt_trans hr0 hp.1
    have ha : 0 ≤ 1 - r / p := by
      rw [sub_nonneg, div_le_one hp0]; exact hp.1.le
    have hb : 1 - r / p ≤ 1 := by
      have : 0 ≤ r / p := div_nonneg hr0.le hp0.le
      linarith
    exact ⟨pow_nonneg ha _, pow_le_one₀ ha hb⟩
  have hint1 := integrand_ii n hn r hr hrEq ρ hρ (fun p => (1 - r / p) ^ n)
    (fun p => (1 - r / p) ^ (n - 1)) (by fun_prop) (by fun_prop)
    (fun p hp => hx01 p hp n) (fun p hp => hx01 p hp (n - 1))
  obtain ⟨-, hD, hlim, hΦ1⟩ := proposition_A_3_phi n hn r hr hrEq
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at hint1 hD ⊢
  set Φ := PhiStar (m + 1) r with hΦdef
  have hΦr : Φ r = 0 := by
    show PhiStar (m + 1) r r = 0
    unfold PhiStar; rw [if_pos le_rfl]
  -- continuity of x ↦ 1 - r/x on [r, 1]
  have hxc : ContinuousOn (fun p : ℝ => 1 - r / p) (Icc r 1) := by
    apply ContinuousOn.sub continuousOn_const
    have hne : ∀ p ∈ Icc r 1, id p ≠ 0 := by
      intro p hp; have := hp.1; simp only [id]; linarith
    exact continuousOn_const.div continuousOn_id hne
  have hxmint : IntervalIntegrable (fun p : ℝ => (1 - r / p) ^ m) volume r 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hr1.le]
    exact hxc.pow m
  -- continuity of Φ on [r, 1]
  have hΦc : ContinuousOn Φ (Icc r 1) := by
    intro p hp
    rcases eq_or_lt_of_le hp.1 with h | h
    · subst h
      have : ContinuousWithinAt Φ (Ioi r) r := by
        rw [ContinuousWithinAt, hΦr]; exact hlim
      exact (continuousWithinAt_Ioi_iff_Ici.mp this).mono Icc_subset_Ici_self
    rcases eq_or_lt_of_le hp.2 with h' | h'
    · subst h'
      set g : ℝ → ℝ := fun v => (v / (v - r)) ^ m * Real.log (v / r) -
        ∑ k ∈ Finset.Ico 1 (m + 1), (1 / (k : ℝ)) * (v / (v - r)) ^ (m - k) with hg
      have hgc : ContinuousAt g 1 := by
        have h1r : (1 : ℝ) - r ≠ 0 := by linarith
        have h1r' : (1 : ℝ) / r ≠ 0 := by positivity
        fun_prop (disch := assumption)
      have hΦg : ∀ y ∈ Ioc r 1, Φ y = g y := by
        intro y hy
        rw [hΦdef]; unfold PhiStar
        rw [if_neg (not_le.mpr hy.1), if_pos hy.2]
        simp [hg]
      have hcont : ContinuousWithinAt Φ (Ioc r 1) 1 :=
        hgc.continuousWithinAt.congr hΦg (hΦg 1 ⟨h, le_rfl⟩)
      apply hcont.mono_of_mem_nhdsWithin
      apply Filter.mem_of_superset (inter_mem_nhdsWithin (Icc r 1) (Ioi_mem_nhds h))
      intro y hy; exact ⟨hy.2, hy.1.2⟩
    · exact (hD p ⟨h, h'⟩).continuousAt.continuousWithinAt
  -- the antiderivative
  set K : ℝ → ℝ := fun p => p - p * Φ p + p * (1 - r / p) ^ m * Φ p with hKdef
  set B : ℝ → ℝ := fun p => (↑m * r / (p - r) - 1 - ↑m * p / (p - r) * (1 - r / p) ^ (m + 1) +
    (↑m + 1) * (1 - r / p) ^ m) * Φ p with hBdef
  have hKc : ContinuousOn K (Icc r 1) := by
    apply ContinuousOn.add
    · exact continuousOn_id.sub (continuousOn_id.mul hΦc)
    · exact (continuousOn_id.mul (hxc.pow m)).mul hΦc
  have hKd : ∀ p ∈ Ioo r 1, HasDerivAt K (B p + (1 - r / p) ^ m) p := by
    intro p hp
    have hp0 : 0 < p := lt_trans hr0 hp.1
    have hpr : 0 < p - r := by linarith [hp.1]
    have hΦd := hD p hp
    have hx : HasDerivAt (fun p : ℝ => 1 - r / p) (r / p ^ 2) p := by
      have h1 := ((hasDerivAt_inv hp0.ne').const_mul r).const_sub 1
      simp only [div_eq_mul_inv]
      exact h1.congr_deriv (by field_simp)
    have hxm := hx.fun_pow m
    have hall := ((hasDerivAt_id p).fun_sub ((hasDerivAt_id p).fun_mul hΦd)).fun_add
      (((hasDerivAt_id p).fun_mul hxm).fun_mul hΦd)
    refine (show HasDerivAt K _ p from hall).congr_deriv ?_
    simp only [hBdef, id]
    rcases m with _ | k
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
      field_simp
      ring
  have hBint : IntervalIntegrable B volume r 1 := hint1
  have hK'int : IntervalIntegrable (fun p => B p + (1 - r / p) ^ m) volume r 1 := hBint.add hxmint
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr1.le hKc hKd hK'int
  have hsplit : ∫ p in r..1, B p = (∫ p in r..1, (B p + (1 - r / p) ^ m)) -
      ∫ p in r..1, (1 - r / p) ^ m := by
    rw [intervalIntegral.integral_add hBint hxmint]; ring
  show r + ∫ p in r..1, B p = value (m + 1) r
  rw [hsplit, hftc]
  simp only [hKdef, hΦr, hΦ1, value, add_tsub_cancel_right]
  ring

end RSPAVal

theorem solution (n : ℕ) (hn : 0 < n) :
    (∃ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 ∧
      ∀ r' ∈ Set.Ioo (0 : ℝ) 1, rEq n r' = 0 → r' = r) ∧
    ∀ r ∈ Set.Ioo (0 : ℝ) (1 / n), rEq n r = 0 →
      (∀ v ∈ Set.Ioc r 1, HasSum
        (fun j : ℕ => 1 / ((j + n : ℕ) : ℝ) * ((v - r) / v) ^ (j + 1)) (PhiStar n r v)) ∧
      (∀ v ∈ Set.Ioo r 1, HasDerivAt (PhiStar n r)
        (1 / v - ((n : ℝ) - 1) * r / (v * (v - r)) * PhiStar n r v) v) ∧
      Filter.Tendsto (PhiStar n r) (nhdsWithin r (Set.Ioi r)) (nhds 0) ∧
      PhiStar n r 1 = 1 ∧
      ∀ ρ G : ProbabilityMeasure ℝ, (∀ t, cdfOf ρ t = PhiStar n r t) →
        (∀ t, cdfOf G t = isoCDF r t) →
        regret (SPA (ρ : Measure ℝ)) (Measure.pi fun _ : Fin n => (G : Measure ℝ)) =
          value n r := by
  refine ⟨RSPARoot.root n hn, fun r hr hrEq => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := proposition_A_3_phi n hn r hr hrEq
  refine ⟨h1, h2, h3, h4, fun ρ G hρ hG => ?_⟩
  rw [RobustSPA.Affiliated.regret_Fstar_eq n hn r hr hrEq ρ hρ G hG]
  exact RSPAVal.value_eq n hn r hr hrEq ρ hρ
