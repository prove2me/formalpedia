-- Prove2me | solution 1 for RamanujanNotebooks.entry_6_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T15:09:24.439693+00:00
-- url     : https://prove2.me/submissions/ecc5a893-f589-4fd6-a846-de8a2ea6a9e3

import Mathlib
import Definitions.Def_RamanujanNotebooks_ch06_ch06EMConstant
import Definitions.Def_RamanujanNotebooks_ch06_ch06PeriodicBernoulli

namespace RNEM
open Real Set MeasureTheory intervalIntegral

noncomputable def Q (j : ℕ) (s : ℝ) : ℝ := bernoulliFun j s / (j.factorial : ℝ)

lemma Q_hasDeriv (j : ℕ) (s : ℝ) : HasDerivAt (Q (j + 1)) (Q j s) s := by
  have h := (hasDerivAt_bernoulliFun (j + 1) s).div_const ((j + 1).factorial : ℝ)
  refine h.congr_deriv ?_
  simp only [Q, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  field_simp

lemma Q_cont (j : ℕ) : Continuous (Q j) := by
  unfold Q; exact (continuous_bernoulliFun j).div_const _

lemma Q_one_eq_zero (j : ℕ) (hj : j ≠ 1) : Q j 1 = Q j 0 := by
  simp [Q, bernoulliFun_endpoints_eq_of_ne_one hj]

lemma Q_zero_val (j : ℕ) : Q j 0 = (bernoulli j : ℝ) / (j.factorial : ℝ) := by
  simp [Q, bernoulliFun_eval_zero]

section
variable (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Ici (0 : ℝ) ⊆ U) (m : ℕ)
  (hf : ContDiffOn ℝ (m : WithTop ℕ∞) f U)
include hU hf

lemma D_hasDeriv (j : ℕ) (hj : j < m) (t : ℝ) (ht : t ∈ U) :
    HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f t) t := by
  have h1 := hf.differentiableOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj)
    hU.uniqueDiffOn t ht
  have h2 : DifferentiableAt ℝ (iteratedDerivWithin j f U) t :=
    h1.differentiableAt (hU.mem_nhds ht)
  have heq : iteratedDerivWithin j f U =ᶠ[nhds t] iteratedDeriv j f :=
    Filter.eventually_of_mem (hU.mem_nhds ht) (fun y hy => iteratedDerivWithin_of_isOpen hU hy)
  have h3 : DifferentiableAt ℝ (iteratedDeriv j f) t := h2.congr_of_eventuallyEq heq.symm
  rw [iteratedDeriv_succ]
  exact h3.hasDerivAt

lemma D_cont (j : ℕ) (hj : j ≤ m) : ContinuousOn (iteratedDeriv j f) U := by
  have h1 := hf.continuousOn_iteratedDerivWithin (m := j) (by exact_mod_cast hj) hU.uniqueDiffOn
  exact h1.congr (fun y hy => (iteratedDerivWithin_of_isOpen hU hy).symm)

/-- integration by parts on `[k, k+1]`, raising the Bernoulli index -/
lemma ibp (k : ℝ) (hk : Icc k (k + 1) ⊆ U) (j : ℕ) (hj : j < m) :
    ∫ t in k..k + 1, Q j (t - k) * iteratedDeriv j f t =
      Q (j + 1) 1 * iteratedDeriv j f (k + 1) - Q (j + 1) 0 * iteratedDeriv j f k
        - ∫ t in k..k + 1, Q (j + 1) (t - k) * iteratedDeriv (j + 1) f t := by
  have hu : ∀ x ∈ uIcc k (k + 1), HasDerivAt (fun t => Q (j + 1) (t - k)) (Q j (x - k)) x := by
    intro x _
    have := (Q_hasDeriv j (x - k)).comp x ((hasDerivAt_id x).sub_const k)
    rw [mul_one] at this
    exact this
  have hv : ∀ x ∈ uIcc k (k + 1), HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f x) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact D_hasDeriv f U hU m hf j hj x (hk hx)
  have hu' : IntervalIntegrable (fun t => Q j (t - k)) volume k (k + 1) :=
    ((Q_cont j).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hv' : IntervalIntegrable (iteratedDeriv (j + 1) f) volume k (k + 1) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (D_cont f U hU m hf (j + 1) hj).mono hk
  have h := integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [add_sub_cancel_left, sub_self] at h
  linarith [h]

lemma unit_em (k : ℝ) (hk : Icc k (k + 1) ⊆ U) (n' : ℕ) (hn : 2 * n' + 1 ≤ m) :
    f (k + 1) = (∫ t in k..k + 1, f t) + (f (k + 1) - f k) / 2
      + (∑ i ∈ Finset.range n', ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f (k + 1) - iteratedDeriv (2 * i + 1) f k))
      + ∫ t in k..k + 1, Q (2 * n' + 1) (t - k) * iteratedDeriv (2 * n' + 1) f t := by
  induction n' with
  | zero =>
    have h := ibp f U hU m hf k hk 0 (by omega)
    have hQ0 : ∀ s, Q 0 s = 1 := fun s => by simp [Q, bernoulliFun_zero]
    have hQ11 : Q 1 1 = 1 / 2 := by simp [Q, bernoulliFun_one]; norm_num
    have hQ10 : Q 1 0 = -1 / 2 := by simp [Q, bernoulliFun_one]; norm_num
    simp only [hQ0, one_mul, iteratedDeriv_zero, hQ11, hQ10] at h
    simp only [Finset.range_zero, Finset.sum_empty, add_zero, mul_zero, zero_add]
    linarith
  | succ n ih =>
    have ih' := ih (by omega)
    have h1 := ibp f U hU m hf k hk (2 * n + 1) (by omega)
    have h2 := ibp f U hU m hf k hk (2 * n + 1 + 1) (by omega)
    have e1 : Q (2 * n + 1 + 1) 1 = ((bernoulli (2 * (n + 1)) : ℚ) : ℝ) / ((2 * (n + 1)).factorial : ℝ) := by
      rw [Q_one_eq_zero _ (by omega), Q_zero_val]; ring_nf
    have e1' : Q (2 * n + 1 + 1) 0 = ((bernoulli (2 * (n + 1)) : ℚ) : ℝ) / ((2 * (n + 1)).factorial : ℝ) := by
      rw [Q_zero_val]; ring_nf
    have hodd : bernoulli (2 * n + 1 + 1 + 1) = 0 :=
      bernoulli_eq_zero_of_odd ⟨n + 1, by ring⟩ (by omega)
    have e2 : Q (2 * n + 1 + 1 + 1) 1 = 0 := by
      rw [Q_one_eq_zero _ (by omega), Q_zero_val, hodd]; simp
    have e2' : Q (2 * n + 1 + 1 + 1) 0 = 0 := by
      rw [Q_zero_val, hodd]; simp
    rw [e1, e1'] at h1
    rw [e2, e2'] at h2
    rw [Finset.sum_range_succ]
    have h3 : 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 := by ring
    rw [h3]
    linarith

lemma P_eq (j : ℕ) (k : ℕ) : EqOn (fun t => RamanujanNotebooks.ch06PeriodicBernoulli j t)
    (fun t => Q j (t - k)) (uIoo (k : ℝ) (k + 1)) := by
  intro t ht
  rw [uIoo_of_le (by linarith)] at ht
  have hfl : ⌊t⌋ = (k : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [ht.1, ht.2]
  simp only [RamanujanNotebooks.ch06PeriodicBernoulli, Q, Int.fract, hfl]
  push_cast; ring_nf

lemma sum_em (hU0 : Ici (0 : ℝ) ⊆ U) (x : ℕ) (n : ℕ) (hn : 2 * n + 1 ≤ m) :
    (∑ k ∈ Finset.range x, f ((k : ℝ) + 1)) = (∫ t in (0 : ℝ)..(x : ℝ), f t) + (f x - f 0) / 2
      + (∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f x - iteratedDeriv (2 * i + 1) f 0))
      + ∫ t in (0 : ℝ)..(x : ℝ), RamanujanNotebooks.ch06PeriodicBernoulli (2 * n + 1) t *
          iteratedDeriv (2 * n + 1) f t := by
  have hk : ∀ k : ℕ, Icc (k : ℝ) (k + 1) ⊆ U := fun k t ht => hU0 (le_trans (by positivity) ht.1)
  have hD : ∀ j ≤ m, ∀ k : ℕ, IntervalIntegrable (iteratedDeriv j f) volume (k : ℝ) ((k : ℝ) + 1) := by
    intro j hj k
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact (D_cont f U hU m hf j hj).mono (hk k)
  have hunit := fun k : ℕ => unit_em f U hU m hf (k : ℝ) (hk k) n hn
  rw [Finset.sum_congr rfl (fun k _ => hunit k)]
  simp only [Finset.sum_add_distrib]
  -- integrals of f
  have hf0 : ∀ k < x, IntervalIntegrable f volume ((fun i : ℕ => (i : ℝ)) k) ((fun i : ℕ => (i : ℝ)) (k + 1)) := by
    intro k _
    have := hD 0 (Nat.zero_le _) k
    simp only [iteratedDeriv_zero] at this
    simpa using this
  have I1 := intervalIntegral.sum_integral_adjacent_intervals hf0
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at I1
  -- integrals of P D
  have hPD : ∀ k < x, IntervalIntegrable (fun t => RamanujanNotebooks.ch06PeriodicBernoulli (2 * n + 1) t *
      iteratedDeriv (2 * n + 1) f t) volume ((fun i : ℕ => (i : ℝ)) k) ((fun i : ℕ => (i : ℝ)) (k + 1)) := by
    intro k _
    have h1 : IntervalIntegrable (fun t => Q (2 * n + 1) (t - k) * iteratedDeriv (2 * n + 1) f t) volume
        (k : ℝ) ((k : ℝ) + 1) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le (by linarith)]
      exact (((Q_cont _).comp (continuous_id.sub continuous_const)).continuousOn).mul
        ((D_cont f U hU m hf _ hn).mono (hk k))
    simp only [Nat.cast_add, Nat.cast_one]
    exact h1.congr_uIoo (fun t ht => by have hP := P_eq f U hU m hf (2 * n + 1) k ht; simp only at hP ⊢; rw [hP])
  have I2 := intervalIntegral.sum_integral_adjacent_intervals hPD
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at I2
  have hPQ : ∀ k : ℕ, ∫ t in (k : ℝ)..(k : ℝ) + 1, Q (2 * n + 1) (t - k) * iteratedDeriv (2 * n + 1) f t =
      ∫ t in (k : ℝ)..(k : ℝ) + 1, RamanujanNotebooks.ch06PeriodicBernoulli (2 * n + 1) t *
        iteratedDeriv (2 * n + 1) f t := by
    intro k
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hP := P_eq f U hU m hf (2 * n + 1) k ht; simp only at hP ⊢; rw [hP]
  simp only [hPQ]
  rw [I1, I2]
  -- telescoping
  have T1 : ∑ k ∈ Finset.range x, (f ((k : ℝ) + 1) - f k) / 2 = (f x - f 0) / 2 := by
    rw [← Finset.sum_div]
    have := Finset.sum_range_sub (fun k : ℕ => f k) x
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]
  have T2 : ∑ k ∈ Finset.range x, ∑ i ∈ Finset.range n,
      ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f ((k : ℝ) + 1) - iteratedDeriv (2 * i + 1) f k) =
      ∑ i ∈ Finset.range n, ((bernoulli (2 * (i + 1)) : ℚ) : ℝ) / ((2 * (i + 1)).factorial : ℝ)
          * (iteratedDeriv (2 * i + 1) f x - iteratedDeriv (2 * i + 1) f 0) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    congr 1
    have := Finset.sum_range_sub (fun k : ℕ => iteratedDeriv (2 * i + 1) f k) x
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
    rw [this]
  rw [T1, T2]

end

open RamanujanNotebooks in
theorem main (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Set.Ici (0 : ℝ) ⊆ U)
    (n : ℕ) (hf : ContDiffOn ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) f U)
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
      (Set.Ioi (0 : ℝ)))
    (a : ℝ) (ha : IntervalIntegrable f MeasureTheory.volume 0 a)
    (x : ℕ) (hx : 1 ≤ x) :
    (∑ k ∈ Finset.range x, f ((k : ℝ) + 1))
      = (∫ t in a..(x : ℝ), f t) + f (x : ℝ) / 2
        + (∑ k ∈ Finset.range n,
            ((bernoulli (2 * (k + 1)) : ℚ) : ℝ) / ((2 * (k + 1)).factorial : ℝ)
              * iteratedDeriv (2 * k + 1) f (x : ℝ))
        - (∫ t in Set.Ioi (x : ℝ),
            ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
        + ch06EMConstant f a n := by
  rw [sum_em f U hU (2 * n + 1) hf hU0 x n le_rfl]
  have hx0 : (0 : ℝ) ≤ x := by positivity
  have h0x : IntervalIntegrable f volume 0 (x : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx0]
    have := D_cont f U hU (2 * n + 1) hf 0 (Nat.zero_le _)
    simp only [iteratedDeriv_zero] at this
    exact this.mono (fun t ht => hU0 ht.1)
  have hF : (∫ t in (0 : ℝ)..(x : ℝ), f t) = (∫ t in (0 : ℝ)..a, f t) + ∫ t in a..(x : ℝ), f t :=
    (intervalIntegral.integral_add_adjacent_intervals ha (ha.symm.trans h0x)).symm
  have hP : (∫ t in Set.Ioi (0 : ℝ), ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) =
      (∫ t in (0 : ℝ)..(x : ℝ), ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t) +
      ∫ t in Set.Ioi (x : ℝ), ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t := by
    rw [intervalIntegral.integral_of_le hx0, ← Ioc_union_Ioi_eq_Ioi hx0]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hx0))
  rw [hF]
  unfold ch06EMConstant
  rw [hP]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end RNEM

open RamanujanNotebooks in
theorem solution (f : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U) (hU0 : Set.Ici (0 : ℝ) ⊆ U)
    (n : ℕ) (hf : ContDiffOn ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) f U)
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
      (Set.Ioi (0 : ℝ)))
    (a : ℝ) (ha : IntervalIntegrable f MeasureTheory.volume 0 a)
    (x : ℕ) (hx : 1 ≤ x) :
    (∑ k ∈ Finset.range x, f ((k : ℝ) + 1))
      = (∫ t in a..(x : ℝ), f t) + f (x : ℝ) / 2
        + (∑ k ∈ Finset.range n,
            ((bernoulli (2 * (k + 1)) : ℚ) : ℝ) / ((2 * (k + 1)).factorial : ℝ)
              * iteratedDeriv (2 * k + 1) f (x : ℝ))
        - (∫ t in Set.Ioi (x : ℝ),
            ch06PeriodicBernoulli (2 * n + 1) t * iteratedDeriv (2 * n + 1) f t)
        + ch06EMConstant f a n :=
  RNEM.main f U hU hU0 n hf hint a ha x hx
