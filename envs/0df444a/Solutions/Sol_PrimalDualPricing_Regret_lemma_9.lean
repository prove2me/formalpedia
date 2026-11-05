-- Prove2me | solution 1 for PrimalDualPricing.Regret.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T13:50:34.561722+00:00
-- url     : https://prove2.me/submissions/2de08496-aab4-4cc6-9949-5eea31488f8d

import Mathlib

open MeasureTheory ProbabilityTheory

/-- Exponential moments of the Poisson weights. -/
lemma pdp9_hasSum_exp (r : ℝ) (c : ℝ) :
    HasSum (fun n : ℕ => Real.exp (-r) * r ^ n / (n.factorial) * Real.exp (c * n))
      (Real.exp (-r) * Real.exp (r * Real.exp c)) := by
  have H := (NormedSpace.expSeries_div_hasSum_exp (r * Real.exp c)).mul_left (Real.exp (-r))
  rw [← Real.exp_eq_exp_ℝ] at H
  convert H using 1
  all_goals first | rfl | (funext n; rw [mul_pow, ← Real.exp_nat_mul]; ring_nf)

/-- Two-sided Chernoff bound for a Poisson variable. -/
lemma pdp9_chernoff (r : ℝ) (hr : 0 < r) (t θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (poissonMeasure r.toNNReal {x : ℕ | t < |(x : ℝ) - r|}).toReal
      ≤ 2 * Real.exp (r * θ ^ 2 - θ * t) := by
  have hcoe : ((r.toNNReal : NNReal) : ℝ) = r := Real.coe_toNNReal _ hr.le
  set S : Set ℕ := {x : ℕ | t < |(x : ℝ) - r|} with hS
  set p : ℕ → ℝ := fun n => Real.exp (-r) * r ^ n / (n.factorial) with hp
  have hp0 : ∀ n, 0 ≤ p n := fun n => by simp only [hp]; positivity
  have h1 : (poissonMeasure r.toNNReal S).toReal = ∑' n, p n * S.indicator 1 n := by
    change (poissonMeasure r.toNNReal).real S = _
    rw [← integral_indicator_one (MeasurableSet.of_discrete), integral_poissonMeasure, hcoe]
    rfl
  rw [h1]
  set g : ℕ → ℝ := fun n => p n * Real.exp (θ * n) * Real.exp (-(θ * (r + t)))
    + p n * Real.exp ((-θ) * n) * Real.exp (θ * (r - t)) with hg
  have hgsum : HasSum g (Real.exp (-r) * Real.exp (r * Real.exp θ) * Real.exp (-(θ * (r + t)))
      + Real.exp (-r) * Real.exp (r * Real.exp (-θ)) * Real.exp (θ * (r - t))) :=
    ((pdp9_hasSum_exp r θ).mul_right _).add ((pdp9_hasSum_exp r (-θ)).mul_right _)
  have hle : ∀ n, p n * S.indicator 1 n ≤ g n := by
    intro n
    have e1 : p n * Real.exp (θ * n) * Real.exp (-(θ * (r + t)))
        = p n * Real.exp (θ * ((n : ℝ) - r - t)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    have e2 : p n * Real.exp ((-θ) * n) * Real.exp (θ * (r - t))
        = p n * Real.exp (θ * (r - n - t)) := by
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    simp only [hg, e1, e2]
    by_cases hn : n ∈ S
    · rw [Set.indicator_of_mem hn, Pi.one_apply, mul_one]
      have hn' : t < |(n : ℝ) - r| := hn
      rcases lt_abs.mp hn' with h | h
      · have : 1 ≤ Real.exp (θ * ((n : ℝ) - r - t)) :=
          Real.one_le_exp (mul_nonneg hθ0 (by linarith))
        nlinarith [hp0 n, Real.exp_pos (θ * (r - n - t))]
      · have : 1 ≤ Real.exp (θ * (r - n - t)) :=
          Real.one_le_exp (mul_nonneg hθ0 (by linarith))
        nlinarith [hp0 n, Real.exp_pos (θ * ((n : ℝ) - r - t))]
    · rw [Set.indicator_of_notMem hn, mul_zero]
      have := hp0 n
      positivity
  have hsum : Summable (fun n => p n * S.indicator 1 n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (hp0 n)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)) hle hgsum.summable
  refine (hasSum_le hle hsum.hasSum hgsum).trans ?_
  have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ0]; exact hθ1
  have hθabs' : |-θ| ≤ 1 := by rw [abs_neg]; exact hθabs
  have b1 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hθabs)).2
  have b2 := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hθabs')).2
  have k1 : Real.exp (-r) * Real.exp (r * Real.exp θ) * Real.exp (-(θ * (r + t)))
      ≤ Real.exp (r * θ ^ 2 - θ * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left b1 hr.le]
  have k2 : Real.exp (-r) * Real.exp (r * Real.exp (-θ)) * Real.exp (θ * (r - t))
      ≤ Real.exp (r * θ ^ 2 - θ * t) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left b2 hr.le
    nlinarith
  linarith

theorem solution (a β γ η q : ℝ) (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ) (hη : 0 < η)
    (hq : 0 < q) :
    ∃ C : ℝ, ∀ r : ℕ → ℝ, (∀ n : ℕ, 1 ≤ n → a * (n : ℝ) ^ β ≤ r n) →
      ∀ n : ℕ, 1 ≤ n →
        (poissonMeasure (r n).toNNReal
            {x : ℕ | r n * (γ * Real.log n ^ (1 / 2 + η) * r n ^ (-(1 / 2 : ℝ)))
              < |(x : ℝ) - r n|}).toReal
          ≤ C / (n : ℝ) ^ q := by
  -- threshold 1: γ (log n)^{1/2+η} ≤ 2 √a n^{β/2}
  have hc : 0 < 2 * Real.sqrt a / γ := by have := Real.sqrt_pos.mpr ha; positivity
  have hO := (isLittleO_log_rpow_rpow_atTop (1 / 2 + η) (show 0 < β / 2 by positivity)).bound hc
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hO)
  -- threshold 2: log n ≥ K
  set K : ℝ := max 1 ((4 * q / γ ^ 2) ^ (1 / (2 * η))) with hK
  set N2 : ℕ := ⌈Real.exp K⌉₊ with hN2
  set N : ℕ := max (max N1 N2) 1 with hN
  refine ⟨2 + (N : ℝ) ^ q, fun r hr n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnq : 0 < (n : ℝ) ^ q := Real.rpow_pos_of_pos hn0 q
  have hNq : 0 ≤ (N : ℝ) ^ q := Real.rpow_nonneg (by positivity) q
  by_cases hnN : n < N
  · -- small n: probability ≤ 1 ≤ C / n^q
    have hP : (poissonMeasure (r n).toNNReal
            {x : ℕ | r n * (γ * Real.log n ^ (1 / 2 + η) * r n ^ (-(1 / 2 : ℝ)))
              < |(x : ℝ) - r n|}).toReal ≤ 1 := by
      change (poissonMeasure (r n).toNNReal).real _ ≤ 1
      exact measureReal_le_one
    refine hP.trans ?_
    rw [le_div_iff₀ hnq, one_mul]
    have : (n : ℝ) ^ q ≤ (N : ℝ) ^ q :=
      Real.rpow_le_rpow hn0.le (by exact_mod_cast hnN.le) hq.le
    linarith
  · push Not at hnN
    have hnN1 : N1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hnN
    have hnN2 : N2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hnN
    set R := r n with hR
    have hRa : a * (n : ℝ) ^ β ≤ R := hr n hn
    have hR0 : 0 < R := lt_of_lt_of_le (by have := Real.rpow_pos_of_pos hn0 β; positivity) hRa
    -- log n ≥ K ≥ 1
    have hlogK : K ≤ Real.log n := by
      have : Real.exp K ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hnN2)
      calc K = Real.log (Real.exp K) := (Real.log_exp K).symm
        _ ≤ Real.log n := Real.log_le_log (Real.exp_pos K) this
    have hK1 : 1 ≤ K := le_max_left _ _
    have hlog0 : 0 < Real.log n := by linarith
    set Lg := Real.log n with hLg
    set L := Lg ^ (1 / 2 + η) with hL
    have hL0 : 0 < L := Real.rpow_pos_of_pos hlog0 _
    set s := Real.sqrt R with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hR0
    have hss : s * s = R := Real.mul_self_sqrt hR0.le
    have hRpow : R ^ (-(1 / 2 : ℝ)) = 1 / s := by
      rw [Real.rpow_neg hR0.le, ← Real.sqrt_eq_rpow, one_div]
    have ht : R * (γ * L * R ^ (-(1 / 2 : ℝ))) = γ * L * s := by
      rw [hRpow, ← hss]; field_simp
    rw [ht]
    -- θ = γ L / (2 s) ≤ 1
    set θ := γ * L / (2 * s) with hθ
    have hθ0 : 0 ≤ θ := by positivity
    have hθ1 : θ ≤ 1 := by
      have hb := hN1 n hnN1
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL0,
        abs_of_nonneg (Real.rpow_nonneg hn0.le _)] at hb
      have h2 : Real.sqrt a * (n : ℝ) ^ (β / 2) ≤ s := by
        have e : Real.sqrt a * (n : ℝ) ^ (β / 2) = Real.sqrt (a * (n : ℝ) ^ β) := by
          rw [Real.sqrt_mul ha.le, Real.sqrt_eq_rpow ((n : ℝ) ^ β), ← Real.rpow_mul hn0.le]
          ring_nf
        rw [e]; exact Real.sqrt_le_sqrt hRa
      have h3 : γ * L ≤ 2 * s := by
        have := mul_le_mul_of_nonneg_left hb hγ.le
        have e : γ * (2 * Real.sqrt a / γ * (n : ℝ) ^ (β / 2))
            = 2 * (Real.sqrt a * (n : ℝ) ^ (β / 2)) := by field_simp
        linarith
      rw [hθ, div_le_one (by positivity)]; exact h3
    have hch := pdp9_chernoff R hR0 (γ * L * s) θ hθ0 hθ1
    refine hch.trans ?_
    have hexp : R * θ ^ 2 - θ * (γ * L * s) = -(γ ^ 2 * L ^ 2 / 4) := by
      rw [hθ, ← hss]; field_simp; ring
    rw [hexp]
    -- γ² L² / 4 ≥ q log n
    have hL2 : L ^ 2 = Lg * Lg ^ (2 * η) := by
      rw [hL, ← Real.rpow_natCast, ← Real.rpow_mul hlog0.le, ← Real.rpow_one_add' hlog0.le]
      · norm_num; ring_nf
      · positivity
    have hpow : 4 * q / γ ^ 2 ≤ Lg ^ (2 * η) := by
      have hb : (4 * q / γ ^ 2) ^ (1 / (2 * η)) ≤ Lg := (le_max_right _ _).trans hlogK
      have := Real.rpow_le_rpow (by positivity) hb (show 0 ≤ 2 * η by positivity)
      rwa [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity),
        Real.rpow_one] at this
    have hkey : q * Lg ≤ γ ^ 2 * L ^ 2 / 4 := by
      rw [hL2]
      have := mul_le_mul_of_nonneg_left hpow hlog0.le
      have e : Lg * (4 * q / γ ^ 2) = 4 * (q * Lg) / γ ^ 2 := by field_simp
      rw [e, div_le_iff₀ (by positivity)] at this
      nlinarith
    have hfin : Real.exp (-(γ ^ 2 * L ^ 2 / 4)) ≤ 1 / (n : ℝ) ^ q := by
      rw [Real.rpow_def_of_pos hn0, one_div, ← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      rw [← hLg]; linarith
    calc 2 * Real.exp (-(γ ^ 2 * L ^ 2 / 4)) ≤ 2 * (1 / (n : ℝ) ^ q) := by linarith
      _ = 2 / (n : ℝ) ^ q := mul_one_div _ _
      _ ≤ (2 + (N : ℝ) ^ q) / (n : ℝ) ^ q :=
          div_le_div_of_nonneg_right (by linarith) hnq.le
