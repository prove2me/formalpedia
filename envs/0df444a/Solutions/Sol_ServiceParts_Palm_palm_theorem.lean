-- Prove2me | solution 1 for ServiceParts.Palm.palm_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T15:54:04.038009+00:00
-- url     : https://prove2.me/submissions/4bb3db6a-8d61-4f81-b101-36041a29cdf5

import Mathlib
import Definitions.Def_ServiceParts_Palm_ResupplySystem
import Theorems.Thm_ServiceParts_Palm_units_binomial_given_orders
import Theorems.Thm_ServiceParts_Palm_order_count_poisson
import Theorems.Thm_ServiceParts_Palm_integral_tail_tendsto_mean

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Topology

namespace ServiceParts.Palm

/-- Poisson thinning series: Σₙ Poi(a)(n) · Bin(n,p)(x) = Poi(a p)(x). -/
lemma palm_thinning_series (a p : ℝ) (x : ℕ) :
    HasSum (fun n : ℕ => Real.exp (-a) * a ^ n / (Nat.factorial n : ℝ) *
      ((Nat.choose n x : ℝ) * p ^ x * (1 - p) ^ (n - x)))
      (Real.exp (-(a * p)) * (a * p) ^ x / (Nat.factorial x : ℝ)) := by
  rw [← hasSum_nat_add_iff' x]
  have hz : ∑ i ∈ Finset.range x, Real.exp (-a) * a ^ i / (Nat.factorial i : ℝ) *
      ((Nat.choose i x : ℝ) * p ^ x * (1 - p) ^ (i - x)) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
    simp
  rw [hz, sub_zero]
  have hexp : HasSum (fun m : ℕ => (a * (1 - p)) ^ m / (Nat.factorial m : ℝ))
      (Real.exp (a * (1 - p))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (a * (1 - p))
  have h2 := hexp.mul_left (Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ))
  have hval : Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ) * Real.exp (a * (1 - p)) =
      Real.exp (-(a * p)) * (a * p) ^ x / (Nat.factorial x : ℝ) := by
    have : Real.exp (-a) * Real.exp (a * (1 - p)) = Real.exp (-(a * p)) := by
      rw [← Real.exp_add]; ring_nf
    calc Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ) * Real.exp (a * (1 - p))
        = (Real.exp (-a) * Real.exp (a * (1 - p))) * (a * p) ^ x / (Nat.factorial x : ℝ) := by
          ring
      _ = _ := by rw [this]
  rw [hval] at h2
  have key : ∀ m : ℕ, Real.exp (-a) * a ^ (m + x) / (Nat.factorial (m + x) : ℝ) *
      ((Nat.choose (m + x) x : ℝ) * p ^ x * (1 - p) ^ (m + x - x)) =
      Real.exp (-a) * (a * p) ^ x / (Nat.factorial x : ℝ) *
        ((a * (1 - p)) ^ m / (Nat.factorial m : ℝ)) := by
    intro m
    have hc : ((Nat.choose (m + x) x : ℕ) : ℝ) * (Nat.factorial m : ℝ) *
        (Nat.factorial x : ℝ) = (Nat.factorial (m + x) : ℝ) := by
      exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial m x
    have hm : (Nat.factorial m : ℝ) ≠ 0 := by positivity
    have hx : (Nat.factorial x : ℝ) ≠ 0 := by positivity
    have hch : ((Nat.choose (m + x) x : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (Nat.le_add_left x m)).ne'
    rw [Nat.add_sub_cancel, ← hc, mul_pow a (1 - p) m, mul_pow a p x, pow_add]
    field_simp
  have hf := funext key
  rw [hf]
  exact h2

/-- Abstract total-probability step, with no measurability assumptions on the level sets. -/
lemma palm_total_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X N : Ω → ℕ) (r : ℕ → ℕ → ℝ) (s : ℕ → ℝ)
    (hr : ∀ y n, (μ ({ω | X ω = y} ∩ {ω | N ω = n})).toReal = r y n)
    (hs : ∀ y, HasSum (fun n => r y n) (s y)) (h1 : HasSum s 1) (x : ℕ) :
    (μ {ω | X ω = x}).toReal = s x := by
  have hr0 : ∀ y n, 0 ≤ r y n := fun y n => hr y n ▸ ENNReal.toReal_nonneg
  have hs0 : ∀ y, 0 ≤ s y := fun y => (hs y).nonneg (hr0 y)
  have ha : ∀ y n, μ ({ω | X ω = y} ∩ {ω | N ω = n}) = ENNReal.ofReal (r y n) := by
    intro y n; rw [← hr y n, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hsumn : ∀ y, ∑' n, μ ({ω | X ω = y} ∩ {ω | N ω = n}) = ENNReal.ofReal (s y) := by
    intro y
    simp_rw [ha y]
    rw [← ENNReal.ofReal_tsum_of_nonneg (hr0 y) (hs y).summable, (hs y).tsum_eq]
  have htot : ∑' y, ENNReal.ofReal (s y) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hs0 h1.summable, h1.tsum_eq, ENNReal.ofReal_one]
  -- upper bound for A
  have hA : μ {ω | X ω = x} ≤ ENNReal.ofReal (s x) := by
    rw [← hsumn x]
    refine (measure_mono ?_).trans (measure_iUnion_le _)
    intro ω hω
    exact Set.mem_iUnion.mpr ⟨N ω, hω, rfl⟩
  -- upper bound for the complement
  have hAc : μ {ω | X ω = x}ᶜ ≤ ∑' y, ite (y = x) 0 (ENNReal.ofReal (s y)) := by
    have hle : {ω | X ω = x}ᶜ ⊆ ⋃ y, ⋃ n,
        (if y = x then (∅ : Set Ω) else {ω | X ω = y} ∩ {ω | N ω = n}) := by
      intro ω hω
      refine Set.mem_iUnion.mpr ⟨X ω, Set.mem_iUnion.mpr ⟨N ω, ?_⟩⟩
      have : X ω ≠ x := hω
      rw [if_neg this]
      exact ⟨rfl, rfl⟩
    refine (measure_mono hle).trans ((measure_iUnion_le _).trans (ENNReal.tsum_le_tsum ?_))
    intro y
    refine (measure_iUnion_le _).trans ?_
    by_cases hy : y = x
    · simp [hy]
    · simp only [if_neg hy]
      rw [hsumn y]
  have hUV : ENNReal.ofReal (s x) + ∑' y, ite (y = x) 0 (ENNReal.ofReal (s y)) = 1 :=
    by convert (ENNReal.tsum_eq_add_tsum_ite (f := fun y => ENNReal.ofReal (s y)) x).symm.trans htot
  have hge : 1 ≤ μ {ω | X ω = x} + μ {ω | X ω = x}ᶜ := by
    rw [← measure_univ (μ := μ), ← Set.union_compl_self {ω | X ω = x}]
    exact measure_union_le _ _
  have heq : μ {ω | X ω = x} = ENNReal.ofReal (s x) := by
    refine le_antisymm hA (not_lt.mp fun hlt => ?_)
    have := ENNReal.add_lt_add_of_lt_of_le (measure_ne_top _ _) hlt hAc
    rw [hUV] at this
    exact absurd hge (not_le.mpr this)
  rw [heq, ENNReal.toReal_ofReal (hs0 x)]

/-- Level-2 reduction: the finite-time Poisson law (a520679d) from the binomial law given the
order count (0a33d0ab) and the Poisson order count (eb0f8fab). -/
theorem palm_finite_time_of_children {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) {t : ℝ} (ht : 0 < t)
    (hbin : ∀ n x : ℕ,
      (P ({ω | S.unitsInResupply t ω = x} ∩ {ω | S.orderCount t ω = n})).toReal =
        (P {ω | S.orderCount t ω = n}).toReal *
          ((Nat.choose n x : ℝ) * ((1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x *
            (1 - (1 / t) * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ (n - x)))
    (hpois : ∀ n : ℕ, (P {ω | S.orderCount t ω = n}).toReal =
      Real.exp (-(S.rate * t)) * (S.rate * t) ^ n / (Nat.factorial n : ℝ)) (x : ℕ) :
    (P {ω | S.unitsInResupply t ω = x}).toReal =
      Real.exp (-(S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) *
        (S.rate * ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)) ^ x / (Nat.factorial x : ℝ) := by
  set I := ∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u)
  have hap : S.rate * t * ((1 / t) * I) = S.rate * I := by
    field_simp
  have hs : ∀ y, HasSum (fun n => (P ({ω | S.unitsInResupply t ω = y} ∩
      {ω | S.orderCount t ω = n})).toReal)
      (Real.exp (-(S.rate * I)) * (S.rate * I) ^ y / (Nat.factorial y : ℝ)) := by
    intro y
    have := palm_thinning_series (S.rate * t) ((1 / t) * I) y
    rw [hap] at this
    simp only [hbin, hpois]
    exact this
  have h1 : HasSum (fun y : ℕ => Real.exp (-(S.rate * I)) * (S.rate * I) ^ y /
      (Nat.factorial y : ℝ)) 1 := by
    have hexp : HasSum (fun m : ℕ => (S.rate * I) ^ m / (Nat.factorial m : ℝ))
        (Real.exp (S.rate * I)) := by
      rw [Real.exp_eq_exp_ℝ]
      exact NormedSpace.expSeries_div_hasSum_exp (S.rate * I)
    have := hexp.mul_left (Real.exp (-(S.rate * I)))
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    simp only [mul_div_assoc]
    exact this
  exact palm_total_prob P (S.unitsInResupply t) (S.orderCount t) _ _ (fun _ _ => rfl) hs h1 x

end ServiceParts.Palm

open ServiceParts.Palm in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (S : ResupplySystem Ω P) (x : ℕ) :
    Tendsto (fun t : ℝ => (P {ω | S.unitsInResupply t ω = x}).toReal) atTop
      (𝓝 (Real.exp (-(S.rate * S.meanResupply)) * (S.rate * S.meanResupply) ^ x /
        (Nat.factorial x : ℝ))) := by
  set φ : ℝ → ℝ := fun m => Real.exp (-(S.rate * m)) * (S.rate * m) ^ x / (Nat.factorial x : ℝ)
    with hφ
  have hφc : Continuous φ := by
    simp only [hφ]; fun_prop
  have h1 : Tendsto (fun t : ℝ => φ (∫ u in (0 : ℝ)..t, (1 - S.resupplyCdf u))) atTop
      (𝓝 (φ S.meanResupply)) :=
    (hφc.tendsto _).comp (ServiceParts.Palm.integral_tail_tendsto_mean S)
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [hφ]
  exact (palm_finite_time_of_children S ht
    (fun n x => ServiceParts.Palm.units_binomial_given_orders S ht n x)
    (fun n => ServiceParts.Palm.order_count_poisson S ht n) x).symm
