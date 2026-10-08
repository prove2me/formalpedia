-- Prove2me | solution 1 for QueueingFundamentals.AdvMarkov.retrial_pgf_equations
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T15:26:14.064994+00:00
-- url     : https://prove2.me/submissions/8b73acbc-b332-4e1b-8031-6a2c31e7d43c

import Mathlib
import Definitions.Def_QueueingFundamentals_AdvMarkov_Retrial



namespace QueueingFundamentals.AdvMarkov

lemma rt_coefB (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hb : RetrialBalance lam mu gam p0 p1) :
    ∀ n : ℕ, lam * p1 n = ((n:ℝ)+1) * gam * p0 (n+1) := by
  obtain ⟨hA, hB, h0⟩ := hb
  intro n
  induction n with
  | zero =>
    have := hA 0
    simp at this
    simp
    linarith
  | succ m ih =>
    have h1 := hB (m+1) (by omega)
    have h2 := hA (m+1)
    simp only [Nat.add_sub_cancel] at h1
    push_cast at *
    linear_combination h1 + ih + h2

lemma rt_coefC (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hb : RetrialBalance lam mu gam p0 p1) :
    ∀ n : ℕ, mu * p1 (n+1) = lam * p0 (n+1) + lam * p1 n := by
  intro n
  have h1 := rt_coefB lam mu gam p0 p1 hb n
  have h2 := hb.1 (n+1)
  push_cast at *
  linear_combination -h2 - h1

lemma rt_summable_pow (p : ℕ → ℝ) (hp : Summable p) (hnn : ∀ n, 0 ≤ p n) (z : ℝ) (hz : |z| ≤ 1) :
    Summable (fun n => z^n * p n) := by
  refine Summable.of_norm_bounded hp (fun n => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg (hnn n)]
  exact mul_le_of_le_one_left (hnn n) (pow_le_one₀ (abs_nonneg _) hz)

lemma rt_hasDerivAt (p : ℕ → ℝ) (hp : Summable p) (hnn : ∀ n, 0 ≤ p n) (z : ℝ) (hz : |z| < 1) :
    HasDerivAt (pgf p) (∑' n : ℕ, (n:ℝ) * z^(n-1) * p n) z := by
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 ≤ r := le_trans (abs_nonneg z) hzr.le
  set B := ∑' n, p n
  have hpB : ∀ n, p n ≤ B := fun n => hp.le_tsum n (fun j _ => hnn j)
  have hsum : Summable (fun n : ℕ => (n:ℝ) * r^(n-1) * B) := by
    apply Summable.mul_right
    rw [← summable_nat_add_iff 1]
    have h1 : Summable (fun n : ℕ => (n:ℝ) * r^n) := by
      have := summable_pow_mul_geometric_of_norm_lt_one 1
        (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0] : ‖r‖ < 1)
      simpa using this
    have h2 : Summable (fun n : ℕ => r^n) := summable_geometric_of_lt_one hr0 hr1
    refine (h1.add h2).congr (fun n => ?_)
    simp only [Nat.add_sub_cancel]
    push_cast; ring
  have hz' : z ∈ Set.Ioo (-r) r := by
    constructor
    · linarith [neg_abs_le z]
    · linarith [le_abs_self z]
  have := hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => (n:ℝ) * r^(n-1) * B)
    (g := fun n y => y^n * p n) (g' := fun n y => (n:ℝ) * y^(n-1) * p n) (t := Set.Ioo (-r) r)
    (y₀ := z) hsum isOpen_Ioo (isPreconnected_Ioo) ?_ ?_ hz' ?_ hz'
  · exact this
  · intro n y _
    have := (hasDerivAt_pow n y).mul_const (p n)
    exact this
  · intro n y hy
    have hy' : |y| ≤ r := abs_le.mpr ⟨hy.1.le, hy.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_nonneg (hnn n), Nat.abs_cast]
    have := hpB n
    have : |y|^(n-1) ≤ r^(n-1) := pow_le_pow_left₀ (abs_nonneg _) hy' _
    have h0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have : (n:ℝ) * |y|^(n-1) ≤ n * r^(n-1) := mul_le_mul_of_nonneg_left this h0
    calc (n:ℝ) * |y|^(n-1) * p n ≤ n * r^(n-1) * p n := mul_le_mul_of_nonneg_right this (hnn n)
      _ ≤ n * r^(n-1) * B := mul_le_mul_of_nonneg_left (hpB n) (by positivity)
  · exact rt_summable_pow p hp hnn z (le_of_lt hz)


lemma rt_summ (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    Summable p0 ∧ Summable p1 := by
  obtain ⟨h0, h1, hs, _⟩ := hp
  refine ⟨Summable.of_nonneg_of_le h0 (fun n => ?_) hs.summable,
    Summable.of_nonneg_of_le h1 (fun n => ?_) hs.summable⟩
  · linarith [h1 n]
  · linarith [h0 n]

lemma rt_P1_identity (lam mu gam : ℝ) (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1)
    (z : ℝ) (hz : |z| ≤ 1) :
    mu * pgf p1 z = lam * pgf p0 z + lam * z * pgf p1 z := by
  obtain ⟨s0, s1⟩ := rt_summ lam mu gam p0 p1 hp
  have H0 := (rt_summable_pow p0 s0 hp.1 z hz).hasSum
  have H1 := (rt_summable_pow p1 s1 hp.2.1 z hz).hasSum
  have H0s := (hasSum_nat_add_iff' 1).mpr H0
  have H1s := (hasSum_nat_add_iff' 1).mpr H1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul] at H0s H1s
  have hb := hp.2.2.2
  have e1 := H1s.mul_left mu
  have e2 := (H0s.mul_left lam).add (H1.mul_left (lam * z))
  have heq : (fun n => mu * (z^(n+1) * p1 (n+1))) =
      (fun n => lam * (z^(n+1) * p0 (n+1)) + lam * z * (z^n * p1 n)) := by
    funext n
    rw [mul_left_comm, rt_coefC lam mu gam p0 p1 hb n]
    ring
  rw [heq] at e1
  have := e1.unique e2
  have h00 := hb.1 0
  simp at h00
  unfold pgf
  linarith

lemma rt_deriv_identity (lam mu gam : ℝ) (hgam : 0 < gam) (p0 p1 : ℕ → ℝ)
    (hp : IsRetrialSteadyState lam mu gam p0 p1) (z : ℝ) (hz : |z| ≤ 1) :
    HasSum (fun n : ℕ => (n:ℝ) * z^(n-1) * p0 n) (lam * pgf p1 z / gam) := by
  obtain ⟨s0, s1⟩ := rt_summ lam mu gam p0 p1 hp
  have H1 := (rt_summable_pow p1 s1 hp.2.1 z hz).hasSum
  have e := (H1.mul_left lam).div_const gam
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.range_one, Finset.sum_singleton, CharP.cast_eq_zero, zero_mul, sub_zero]
  refine e.congr_fun (fun n => ?_)
  have := rt_coefB lam mu gam p0 p1 hp.2.2.2 n
  simp only [Nat.add_sub_cancel]
  push_cast
  field_simp
  rw [mul_assoc (z^n), this]
  ring

theorem rt_eqs_core (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableAt ℝ (pgf p0) z ∧
      lam * pgf p0 z + z * gam * deriv (pgf p0) z = mu * pgf p1 z ∧
      (lam + mu) * pgf p1 z = lam * pgf p0 z + gam * deriv (pgf p0) z + lam * z * pgf p1 z ∧
      deriv (pgf p0) z = lam * ρ / (gam * (1 - ρ * z)) * pgf p0 z := by
  intro z hz
  have hz1 : |z| < 1 := abs_lt.mpr hz
  obtain ⟨s0, s1⟩ := rt_summ lam mu gam p0 p1 hp
  have hd := rt_hasDerivAt p0 s0 hp.1 z hz1
  have hD := (rt_deriv_identity lam mu gam hgam p0 p1 hp z hz1.le).tsum_eq
  rw [hD] at hd
  have hdv := hd.deriv
  have hI := rt_P1_identity lam mu gam p0 p1 hp z hz1.le
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hρz : 0 < 1 - ρ * z := by
    have : ρ * z ≤ ρ * |z| := mul_le_mul_of_nonneg_left (le_abs_self z) hρ0.le
    nlinarith
  refine ⟨hd.differentiableAt, ?_, ?_, ?_⟩
  · rw [hdv]; field_simp; linarith
  · rw [hdv]; field_simp; linarith
  · rw [hdv, hρ]
    rw [hρ] at hρz
    field_simp
    have hmu' : mu - lam * z ≠ 0 := by
      intro h
      have : 1 - lam / mu * z = (mu - lam * z) / mu := by field_simp
      rw [this, h] at hρz; simp at hρz
    have : pgf p1 z = lam * pgf p0 z / (mu - lam * z) := by
      field_simp; linarith
    rw [this]

end QueueingFundamentals.AdvMarkov

open QueueingFundamentals.AdvMarkov


theorem solution (lam mu gam : ℝ) (hlam : 0 < lam) (hmu : 0 < mu) (hgam : 0 < gam)
    (ρ : ℝ) (hρ : ρ = lam / mu) (hρ1 : ρ < 1)
    (p0 p1 : ℕ → ℝ) (hp : IsRetrialSteadyState lam mu gam p0 p1) :
    ∀ z ∈ Set.Ioo (-1 : ℝ) 1,
      DifferentiableAt ℝ (pgf p0) z ∧
      lam * pgf p0 z + z * gam * deriv (pgf p0) z = mu * pgf p1 z ∧
      (lam + mu) * pgf p1 z = lam * pgf p0 z + gam * deriv (pgf p0) z + lam * z * pgf p1 z ∧
      deriv (pgf p0) z = lam * ρ / (gam * (1 - ρ * z)) * pgf p0 z := by
  exact rt_eqs_core lam mu gam hlam hmu hgam ρ hρ hρ1 p0 p1 hp
