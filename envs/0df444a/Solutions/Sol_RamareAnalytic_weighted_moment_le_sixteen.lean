-- Prove2me | solution 1 for RamareAnalytic.weighted_moment_le_sixteen
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:33:31.530952+00:00
-- url     : https://prove2.me/submissions/b6d900f0-e713-42b6-879c-abbe52c6577c

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.List.Basic

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0
open scoped BigOperators Topology
open Filter

/-! Quantitative weighted absolute moment for Ramaré's multiplicative
correction. Qualitative convergence, finite factors, and the prime tail are
proved in the included components before the final theorem. -/

-- BEGIN COMPONENT EulerSummability.lean
namespace RamareAnalytic


/-- A converse convergence criterion obtained from finite smooth-number Euler
products.  The local bound is on the complete prime-power series. -/
theorem summable_of_local_euler_majorant
    (f g : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_mul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, Nat.Prime p →
      Summable (fun k : ℕ => ‖f (p ^ k)‖))
    (hg_nonneg : ∀ n, 0 ≤ g n) (hg : Summable g)
    (hfactor : ∀ p : ℕ, Nat.Prime p → (∑' k : ℕ, f (p ^ k)) ≤ 1 + g p) :
    Summable f := by
  classical
  apply summable_of_sum_range_le hf_nonneg (c := Real.exp (∑' n : ℕ, g n))
  intro N
  have hs := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hf_mul hlocal N
  have hi : HasSum ((Nat.smoothNumbers N).indicator f)
      (∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k)) :=
    hasSum_subtype_iff_indicator.mp hs.2
  have hsum : (∑ n ∈ Finset.range N, f n) =
      ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator f n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [Set.indicator_apply, hf0]
    · exact (Set.indicator_of_mem
        (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
          (Finset.mem_range.mp hn)) f).symm
  calc
    (∑ n ∈ Finset.range N, f n) =
        ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator f n := hsum
    _ ≤ ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k) := by
      apply sum_le_hasSum _ _ hi
      intro n hn
      by_cases hm : n ∈ Nat.smoothNumbers N
      · simpa only [Set.indicator_of_mem hm] using hf_nonneg n
      · simp only [Set.indicator_of_notMem hm, le_refl]
    _ ≤ ∏ p ∈ Nat.primesBelow N, (1 + g p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg (fun k => hf_nonneg (p ^ k))
      · intro p hp
        exact hfactor p (Nat.mem_primesBelow.mp hp).2
    _ ≤ Real.exp (∑ p ∈ Nat.primesBelow N, g p) :=
      Real.prod_one_add_le_exp_sum _ hg_nonneg
    _ ≤ Real.exp (∑' n : ℕ, g n) := by
      apply Real.exp_le_exp.mpr
      exact hg.sum_le_tsum _ (fun n hn => hg_nonneg n)

private theorem prime_power_tsum_three (f : ℕ → ℝ) (p : ℕ)
    (hz : ∀ k : ℕ, 3 ≤ k → f (p ^ k) = 0) :
    (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range 3) (by
    intro k hk
    apply hz k
    simpa only [Finset.mem_range, not_lt] using hk)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]

private theorem power_div_prime_denominator_le (x s : ℝ) (hx : 2 ≤ x) :
    x ^ s / (x * (x - 1)) ≤ 2 * x ^ (s - 2) := by
  have hx0 : 0 < x := by linarith
  have hden : 0 < x * (x - 1) := mul_pos hx0 (by linarith)
  have hrecip : 1 / (x * (x - 1)) ≤ 2 / x ^ 2 := by
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hx0)).mpr
    nlinarith
  calc
    x ^ s / (x * (x - 1)) = x ^ s * (1 / (x * (x - 1))) := by ring
    _ ≤ x ^ s * (2 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hrecip (Real.rpow_nonneg hx0.le _)
    _ = 2 * x ^ (s - 2) := by
      rw [Real.rpow_sub hx0, Real.rpow_two]
      ring

/-- The weighted absolute moment exists for every multiplicative function
with Ramaré's exact prime-power factors. -/
theorem weighted_summable_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)
  let g : ℕ → ℝ := fun n =>
    2 * (n : ℝ) ^ (-(8 / 5 : ℝ)) + 2 * (n : ℝ) ^ (-(6 / 5 : ℝ))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → f (p ^ k) = 0 := by
    intro p k hp hk
    simp only [f, hpz p k hp hk, abs_zero, zero_mul]
  have hgsum : Summable g := by
    exact ((Real.summable_nat_rpow.mpr (by norm_num : -(8 / 5 : ℝ) < -1)).mul_left 2).add
      ((Real.summable_nat_rpow.mpr (by norm_num : -(6 / 5 : ℝ) < -1)).mul_left 2)
  apply summable_of_local_euler_majorant f g
  · simp [f]
  · simp [f, hmul.1]
  · exact hf_nonneg
  · intro m n hmn
    simp only [f, hmul.2 hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  · intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 3)
    intro k hk
    have hk3 : 3 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [hfz p k hp hk3, norm_zero]
  · intro n
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · exact hgsum
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hcoef : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
      div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (by linarith))
    have hsquare : ((p ^ 2 : ℕ) : ℝ) ^ (2 / 5 : ℝ) =
        (p : ℝ) ^ (4 / 5 : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      norm_num
    rw [prime_power_tsum_three f p (fun k hk => hfz p k hp hk)]
    have hform : f 1 + f p + f (p ^ 2) =
        1 + ((p : ℝ) ^ (2 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
          (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
      simp only [f, hmul.1, (hpv p hp).1, (hpv p hp).2, Nat.cast_one,
        Real.one_rpow, abs_one, one_mul, abs_neg, abs_of_nonneg hcoef, hsquare]
      ring
    rw [hform]
    have hfirst := power_div_prime_denominator_le (p : ℝ) (2 / 5 : ℝ) hp2
    have hsecond := power_div_prime_denominator_le (p : ℝ) (4 / 5 : ℝ) hp2
    norm_num at hfirst hsecond
    simpa only [g] using add_le_add_right (add_le_add hfirst hsecond) 1

/-- Absolute summability follows from the weighted moment, including the
zero index enforced by `ArithmeticFunction`. -/
theorem norm_summable_of_weighted_summable (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) :
    Summable (fun n : ℕ => ‖h n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg (h n)) _ hw
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hw1 : 1 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    simpa only [Real.norm_eq_abs, mul_one] using
      mul_le_mul_of_nonneg_left hw1 (abs_nonneg (h n))

/-- The logarithmic moment is absolutely convergent; the harmless factor 5/2
comes from `log x ≤ x^(2/5)/(2/5)`. -/
theorem log_summable_of_weighted_summable (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) :
    Summable (fun n : ℕ => h n * Real.log (n : ℝ)) := by
  apply (hw.mul_left (5 / 2 : ℝ)).of_norm_bounded
  intro n
  have hlog : ‖Real.log (n : ℝ)‖ ≤ (n : ℝ) ^ (2 / 5 : ℝ) / (2 / 5 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1)]
      exact Real.log_natCast_le_rpow_div n (by norm_num)
  calc
    ‖h n * Real.log (n : ℝ)‖ = |h n| * ‖Real.log (n : ℝ)‖ := by
      rw [norm_mul, Real.norm_eq_abs (h n)]
    _ ≤ |h n| * ((n : ℝ) ^ (2 / 5 : ℝ) / (2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg (h n))
    _ = (5 / 2 : ℝ) * (|h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by ring

/-- The signed Euler factors cancel exactly. Convergence is proved from the
prime-power values, so this result assumes no mass or convergence premise. -/
theorem hasSum_one_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) 1 := by
  have hw := weighted_summable_of_prime_power_values h hmul hpv hpz
  have hn := norm_summable_of_weighted_summable h hw
  have hfactor : ∀ p : Nat.Primes, (∑' k : ℕ, h ((p : ℕ) ^ k)) = 1 := by
    intro p
    rw [prime_power_tsum_three (fun n => h n) (p : ℕ)
      (fun k hk => hpz (p : ℕ) k p.property hk)]
    rw [hmul.1, (hpv (p : ℕ) p.property).1, (hpv (p : ℕ) p.property).2]
    ring
  have hmass : (∑' n : ℕ, h n) = 1 := by
    rw [← hmul.eulerProduct_tprod hn]
    simp only [hfactor, tprod_one]
  exact hmass ▸ hn.of_norm.hasSum

/-- All qualitative hypotheses of the harmonic-convolution error transfer
follow from the exact coefficient factorization. Quantitative moment bounds
are deliberately separate. -/
theorem moments_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) 1 ∧
      Summable (fun n : ℕ => h n * Real.log (n : ℝ)) ∧
      Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by
  have hw := weighted_summable_of_prime_power_values h hmul hpv hpz
  exact ⟨hasSum_one_of_prime_power_values h hmul hpv hpz,
    log_summable_of_weighted_summable h hw, hw⟩

end RamareAnalytic
-- END COMPONENT EulerSummability.lean

-- BEGIN COMPONENT FinitePrimeProduct.lean
namespace RamareFiniteConstants

private structure ProductRow where
  prime : ℕ
  rootUpper : ℕ
  after : ℕ
  deriving DecidableEq

private def rootScale : ℕ := 100000000
private def roundScale : ℕ := 1000000000000

private def denominator (p : ℕ) : ℕ := p * (p - 1)

private noncomputable def factor (p : ℕ) : ℝ :=
  1 + ((p : ℝ) ^ ((2 : ℝ) / 5) + (p : ℝ) ^ ((4 : ℝ) / 5)) /
    (denominator p : ℝ)

private theorem factor_one_le (p : ℕ) : 1 ≤ factor p := by
  unfold factor
  exact le_add_of_nonneg_right (div_nonneg
    (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (Real.rpow_nonneg (Nat.cast_nonneg p) _)) (Nat.cast_nonneg _))

private theorem factor_nonneg (p : ℕ) : 0 ≤ factor p :=
  le_trans (by norm_num) (factor_one_le p)

private theorem root_upper (p u : ℕ)
    (h : p ^ 2 * rootScale ^ 5 ≤ u ^ 5) :
    (p : ℝ) ^ ((2 : ℝ) / 5) ≤ (u : ℝ) / (rootScale : ℝ) := by
  have hS : (0 : ℝ) < (rootScale : ℝ) := by norm_num [rootScale]
  have hpow : ((p : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) = (p : ℝ) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (div_nonneg (Nat.cast_nonneg u) hS.le) (by decide : (5 : ℕ) ≠ 0)).mp
  rw [hpow, div_pow]
  apply (le_div_iff₀ (pow_pos hS 5)).2
  exact_mod_cast h

private theorem factor_upper (p u : ℕ) (hp : 2 ≤ p)
    (h : p ^ 2 * rootScale ^ 5 ≤ u ^ 5) :
    factor p ≤
      ((denominator p * rootScale ^ 2 + u * rootScale + u ^ 2 : ℕ) : ℝ) /
        ((denominator p * rootScale ^ 2 : ℕ) : ℝ) := by
  have hS : (0 : ℝ) < (rootScale : ℝ) := by norm_num [rootScale]
  have hqNat : 0 < denominator p := by
    unfold denominator
    exact Nat.mul_pos (by omega) (by omega)
  have hq : (0 : ℝ) < (denominator p : ℝ) := by exact_mod_cast hqNat
  have hu : 0 ≤ (u : ℝ) / (rootScale : ℝ) := div_nonneg (Nat.cast_nonneg u) hS.le
  have ht := root_upper p u h
  have hx := Real.rpow_nonneg (Nat.cast_nonneg p) ((2 : ℝ) / 5)
  have hfour : (p : ℝ) ^ ((4 : ℝ) / 5) =
      ((p : ℝ) ^ ((2 : ℝ) / 5)) ^ (2 : ℕ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    norm_num
  have hsquare : (p : ℝ) ^ ((4 : ℝ) / 5) ≤
      ((u : ℝ) / (rootScale : ℝ)) ^ (2 : ℕ) := by
    rw [hfour]
    nlinarith
  calc
    factor p ≤ 1 + ((u : ℝ) / (rootScale : ℝ) +
        ((u : ℝ) / (rootScale : ℝ)) ^ (2 : ℕ)) / (denominator p : ℝ) := by
      unfold factor
      exact add_le_add_right (div_le_div_of_nonneg_right (add_le_add ht hsquare) hq.le) 1
    _ = _ := by
      push_cast
      field_simp [ne_of_gt hS, ne_of_gt hq]
      <;> ring

private theorem rounded_step (a p u b : ℕ) (hp : 2 ≤ p)
    (hroot : p ^ 2 * rootScale ^ 5 ≤ u ^ 5)
    (hstep : a * (denominator p * rootScale ^ 2 + u * rootScale + u ^ 2) ≤
      b * (denominator p * rootScale ^ 2)) :
    (a : ℝ) / (roundScale : ℝ) * factor p ≤ (b : ℝ) / (roundScale : ℝ) := by
  have hD : (0 : ℝ) < (roundScale : ℝ) := by norm_num [roundScale]
  have hS : (0 : ℝ) < (rootScale : ℝ) := by norm_num [rootScale]
  have hqNat : 0 < denominator p := by
    unfold denominator
    exact Nat.mul_pos (by omega) (by omega)
  have hden : (0 : ℝ) < ((denominator p * rootScale ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos hqNat (pow_pos (by decide : 0 < rootScale) 2)
  have hstepReal :
      (a : ℝ) * ((denominator p * rootScale ^ 2 + u * rootScale + u ^ 2 : ℕ) : ℝ) ≤
        (b : ℝ) * ((denominator p * rootScale ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hstep
  calc
    (a : ℝ) / (roundScale : ℝ) * factor p ≤
        (a : ℝ) / (roundScale : ℝ) *
          (((denominator p * rootScale ^ 2 + u * rootScale + u ^ 2 : ℕ) : ℝ) /
            ((denominator p * rootScale ^ 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (factor_upper p u hp hroot)
        (div_nonneg (Nat.cast_nonneg a) hD.le)
    _ ≤ (b : ℝ) / (roundScale : ℝ) := by
      rw [div_mul_div_comm]
      apply (div_le_div_iff₀ (mul_pos hD hden) hD).2
      nlinarith [mul_le_mul_of_nonneg_right hstepReal hD.le]

private def productCheck (a : ℕ) : List ProductRow → Bool
  | [] => decide (a ≤ 11150000000000)
  | r :: rs =>
      decide (2 ≤ r.prime ∧
        r.prime ^ 2 * rootScale ^ 5 ≤ r.rootUpper ^ 5 ∧
        a * (denominator r.prime * rootScale ^ 2 +
          r.rootUpper * rootScale + r.rootUpper ^ 2) ≤
          r.after * (denominator r.prime * rootScale ^ 2)) &&
      productCheck r.after rs

private theorem factor_list_nonneg (rs : List ProductRow) :
    0 ≤ (rs.map (fun r => factor r.prime)).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨r, _, rfl⟩ := List.mem_map.mp hx
  exact factor_nonneg r.prime

private theorem productCheck_sound (rs : List ProductRow) :
    ∀ a, productCheck a rs = true →
      (a : ℝ) / (roundScale : ℝ) * (rs.map (fun r => factor r.prime)).prod ≤
        (223 : ℝ) / 20 := by
  induction rs with
  | nil =>
      intro a h
      have ha : a ≤ 11150000000000 := of_decide_eq_true h
      have har : (a : ℝ) ≤ 11150000000000 := by exact_mod_cast ha
      simp only [List.map_nil, List.prod_nil, mul_one]
      calc
        (a : ℝ) / (roundScale : ℝ) ≤ 11150000000000 / (roundScale : ℝ) :=
          div_le_div_of_nonneg_right har (Nat.cast_nonneg roundScale)
        _ = (223 : ℝ) / 20 := by norm_num [roundScale]
  | cons r rs ih =>
      intro a h
      have hparts := Bool.and_eq_true_iff.mp h
      have hrow : 2 ≤ r.prime ∧
          r.prime ^ 2 * rootScale ^ 5 ≤ r.rootUpper ^ 5 ∧
          a * (denominator r.prime * rootScale ^ 2 +
            r.rootUpper * rootScale + r.rootUpper ^ 2) ≤
            r.after * (denominator r.prime * rootScale ^ 2) :=
        of_decide_eq_true hparts.1
      have hstep := rounded_step a r.prime r.rootUpper r.after
        hrow.1 hrow.2.1 hrow.2.2
      have htail := ih r.after hparts.2
      simp only [List.map_cons, List.prod_cons]
      calc
        (a : ℝ) / (roundScale : ℝ) *
            (factor r.prime * (rs.map (fun r => factor r.prime)).prod) =
          ((a : ℝ) / (roundScale : ℝ) * factor r.prime) *
            (rs.map (fun r => factor r.prime)).prod := by ring
        _ ≤ ((r.after : ℝ) / (roundScale : ℝ)) *
            (rs.map (fun r => factor r.prime)).prod :=
          mul_le_mul_of_nonneg_right hstep (factor_list_nonneg rs)
        _ ≤ (223 : ℝ) / 20 := htail

-- Each row gives a prime index, an upper fifth-root numerator, and a rounded
-- upper product numerator. All three columns are literal natural numbers.
private def rows : List ProductRow :=
  [
    ⟨2, 131950792, 2530304535472⟩,
    ⟨3, 155184558, 4200335168941⟩,
    ⟨5, 190365394, 5361213777422⟩,
    ⟨7, 217790643, 6244688559324⟩,
    ⟨11, 260949864, 6779403176034⟩,
    ⟨13, 278982744, 7238880033006⟩,
    ⟨17, 310584351, 7578258620401⟩,
    ⟨19, 324714320, 7883850396055⟩,
    ⟨23, 350502512, 8129873679008⟩,
    ⟨29, 384555653, 8316438876789⟩,
    ⟨31, 394952328, 8491247358483⟩,
    ⟨37, 423916860, 8632830104696⟩,
    ⟨41, 441685908, 8758772058601⟩,
    ⟨43, 450181229, 8878892973091⟩,
    ⟨47, 466486568, 8987418497060⟩,
    ⟨53, 489452271, 9081502274291⟩,
    ⟨59, 510905767, 9164333239230⟩,
    ⟨61, 517764100, 9244422519117⟩,
    ⟨67, 537563684, 9316072246377⟩,
    ⟨71, 550178152, 9383124313501⟩,
    ⟨73, 556325727, 9448308265280⟩,
    ⟨79, 574183670, 9507663827921⟩,
    ⟨83, 585640681, 9563756959601⟩,
    ⟨89, 602221149, 9615396903343⟩,
    ⟨97, 623316601, 9661951372076⟩,
    ⟨101, 633473643, 9706399813362⟩,
    ⟨103, 638461759, 9749959393025⟩,
    ⟨107, 648266398, 9791658131675⟩,
    ⟨109, 653086339, 9832567366610⟩,
    ⟨113, 662569405, 9871821122678⟩,
    ⟨127, 694258952, 9905838953587⟩,
    ⟨131, 702924238, 9938668108412⟩,
    ⟨137, 715629487, 9969803179222⟩,
    ⟨139, 719790185, 10000472300492⟩,
    ⟨149, 740072910, 10028666775676⟩,
    ⟨151, 744030569, 10056471842949⟩,
    ⟨157, 755718165, 10083024745632⟩,
    ⟨163, 767140731, 10108425864237⟩,
    ⟨167, 774616224, 10133129625927⟩,
    ⟨173, 785630692, 10156823722197⟩,
    ⟨179, 796418267, 10179581863644⟩,
    ⟨181, 799965818, 10202076361571⟩,
    ⟨191, 817359938, 10223155590440⟩,
    ⟨193, 820772740, 10244005386440⟩,
    ⟨197, 827535228, 10264369448154⟩,
    ⟨199, 830885597, 10284518357839⟩,
    ⟨211, 850575722, 10303284798429⟩,
    ⟨223, 869604834, 10320833079599⟩,
    ⟨227, 875810894, 10338026269622⟩,
    ⟨229, 878889332, 10355060993199⟩,
    ⟨233, 884998162, 10371759842455⟩,
    ⟨239, 894044551, 10387964602472⟩,
    ⟨241, 897029689, 10404027248341⟩,
    ⟨251, 911736809, 10419321378795⟩,
    ⟨257, 920392878, 10434194667680⟩,
    ⟨263, 928928526, 10448668028946⟩,
    ⟨269, 937348119, 10462760893993⟩,
    ⟨271, 940129578, 10476743509270⟩,
    ⟨277, 948400792, 10490369142950⟩,
    ⟨281, 953855368, 10503771770829⟩,
    ⟨283, 956565194, 10517073883041⟩,
    ⟨293, 969944865, 10529831010657⟩,
    ⟨307, 988223894, 10541885122238⟩,
    ⟨311, 993354254, 10553760877840⟩,
    ⟨313, 995904593, 10565555901075⟩,
    ⟨317, 1000976093, 10577179686948⟩,
    ⟨331, 1018430032, 10588209495299⟩,
    ⟨337, 1025774646, 10599007829669⟩,
    ⟨347, 1037843310, 10609432777492⟩,
    ⟨349, 1040231908, 10619793996551⟩,
    ⟨353, 1044984581, 10630020054375⟩,
    ⟨359, 1052053389, 10640044653029⟩,
    ⟨367, 1061369066, 10649808770165⟩,
    ⟨373, 1068276151, 10659387746097⟩,
    ⟨379, 1075116889, 10668787965775⟩,
    ⟨383, 1079641351, 10678075115451⟩,
    ⟨389, 1086375195, 10687193408451⟩,
    ⟨397, 1095257417, 10696092703927⟩,
    ⟨401, 1099658282, 10704889734482⟩,
    ⟨409, 1108381640, 10713481692937⟩,
    ⟨419, 1119143069, 10721827735794⟩,
    ⟨421, 1121276806, 10730131296919⟩,
    ⟨431, 1131855299, 10738203831514⟩,
    ⟨433, 1133953273, 10746236389576⟩,
    ⟨439, 1140212528, 10754139529689⟩,
    ⟨443, 1144356895, 10761960418663⟩,
    ⟨449, 1150531561, 10769658105326⟩,
    ⟨457, 1158687923, 10777195225142⟩,
    ⟨461, 1162733995, 10784656950083⟩,
    ⟨463, 1164749135, 10792084065216⟩,
    ⟨467, 1168763802, 10799437835420⟩,
    ⟨479, 1180685434, 10806569885998⟩,
    ⟨487, 1188533931, 10813562347436⟩,
    ⟨491, 1192429185, 10820489114287⟩,
    ⟨499, 1200162958, 10827283575305⟩,
    ⟨503, 1204001961, 10834015716997⟩,
    ⟨509, 1209726274, 10840654303517⟩,
    ⟨521, 1221054615, 10847108917739⟩,
    ⟨523, 1222927400, 10853536956639⟩,
    ⟨541, 1239592404, 10859706199214⟩,
    ⟨547, 1245073331, 10865795662265⟩,
    ⟨557, 1254128618, 10871754115588⟩,
    ⟨563, 1259515041, 10877637704028⟩,
    ⟨569, 1264867130, 10883448147352⟩,
    ⟨571, 1266643630, 10889236637166⟩,
    ⟨577, 1271950837, 10894954161393⟩,
    ⟨587, 1280723094, 10900554980160⟩,
    ⟨593, 1285943470, 10906088985881⟩,
    ⟨599, 1291132250, 10911557636505⟩,
    ⟨601, 1292854910, 10917006635117⟩,
    ⟨607, 1298002344, 10922392130221⟩,
    ⟨613, 1303119339, 10927715475895⟩,
    ⟨617, 1306513994, 10932998974851⟩,
    ⟨619, 1308206371, 10938264027859⟩,
    ⟨631, 1318292386, 10943408679925⟩,
    ⟨641, 1326609833, 10948457187821⟩,
    ⟨643, 1328263961, 10953488714627⟩,
    ⟨647, 1331562980, 10958484316710⟩,
    ⟨653, 1336488643, 10963425798313⟩,
    ⟨659, 1341387225, 10968314232897⟩,
    ⟨661, 1343014136, 10973186663459⟩,
    ⟨673, 1352714128, 10977954645554⟩,
    ⟨677, 1355924374, 10982690085703⟩,
    ⟨683, 1360718476, 10987376475994⟩,
    ⟨691, 1367071467, 10991998256933⟩,
    ⟨701, 1374950956, 10996541075373⟩,
    ⟨709, 1381206121, 11001022856055⟩,
    ⟨719, 1388965813, 11005429987616⟩,
    ⟨727, 1395127067, 11009779372614⟩,
    ⟨733, 1399721360, 11014086777810⟩,
    ⟨739, 1404293144, 11018352945728⟩,
    ⟨743, 1407328639, 11022592570657⟩,
    ⟨751, 1413370345, 11026778421501⟩,
    ⟨757, 1417876328, 11030925151061⟩,
    ⟨761, 1420868423, 11035046687980⟩,
    ⟨769, 1426824428, 11039117173845⟩,
    ⟨773, 1429788494, 11043163312273⟩,
    ⟨787, 1440090857, 11047122740293⟩,
    ⟨797, 1447382538, 11051022688241⟩,
    ⟨809, 1456060461, 11054853126483⟩,
    ⟨811, 1457499256, 11058673301794⟩,
    ⟨821, 1464661490, 11062437770363⟩,
    ⟨823, 1466087646, 11066192296965⟩,
    ⟨827, 1468933732, 11069925825373⟩,
    ⟨829, 1470353678, 11073649563503⟩,
    ⟨839, 1477422758, 11077320168767⟩,
    ⟨853, 1487235052, 11080918216668⟩,
    ⟨857, 1490020793, 11084496842526⟩,
    ⟨859, 1491410738, 11088066405779⟩,
    ⟨863, 1494184815, 11091616834052⟩,
    ⟨877, 1503833785, 11095099007133⟩,
    ⟨881, 1506573637, 11098562893219⟩,
    ⟨883, 1507940764, 11102018241160⟩,
    ⟨887, 1510669455, 11105455565123⟩,
    ⟨907, 1524203361, 11108801243688⟩,
    ⟨911, 1526888594, 11112129927872⟩,
    ⟨919, 1532237915, 11115424118935⟩,
    ⟨929, 1538885423, 11118675869515⟩,
    ⟨937, 1544172580, 11121894572242⟩,
    ⟨941, 1546806005, 11125097444283⟩,
    ⟨947, 1550743579, 11128276384177⟩,
    ⟨953, 1554666213, 11131431720186⟩,
    ⟨967, 1563761764, 11134532058986⟩,
    ⟨971, 1566345963, 11137617618104⟩,
    ⟨977, 1570210314, 11140680829077⟩,
    ⟨983, 1574060451, 11143721989082⟩,
    ⟨991, 1579172098, 11146733927520⟩,
    ⟨997, 1582989607, 11149724488315⟩
  ]

private def listed : List ℕ := rows.map ProductRow.prime

private def smallDivisors : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

private theorem checked_product : productCheck roundScale rows = true := by
  decide +kernel

private theorem listed_nodup : listed.Nodup := by
  decide +kernel

-- For each integer omitted from the list, a proper divisor rules out primality.
private theorem checked_coverage :
    ∀ n : Fin 1001, 2 ≤ n.val → n.val ∈ listed ∨
      (smallDivisors.any (fun d => decide (2 ≤ d ∧ d < n.val ∧ n.val % d = 0))) = true := by
  decide +kernel

private theorem prime_mem_listed (p : ℕ) (hp : p.Prime) (hbound : p ≤ 1000) :
    p ∈ listed := by
  have hc := checked_coverage ⟨p, by omega⟩ hp.two_le
  rcases hc with hc | hc
  · exact hc
  · obtain ⟨d, _, hd⟩ := List.any_eq_true.mp hc
    have hdiv : 2 ≤ d ∧ d < p ∧ p % d = 0 := of_decide_eq_true hd
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdiv.2.2) with he | he
    · omega
    · omega

private theorem listed_product_le : (listed.map factor).prod ≤ (223 : ℝ) / 20 := by
  have h := productCheck_sound rows roundScale checked_product
  simpa only [listed, List.map_map, Function.comp_def, div_self
    (show (roundScale : ℝ) ≠ 0 by norm_num [roundScale]), one_mul] using h

/-- A finite Euler-factor bound used in the weighted absolute-moment estimate.
The statement is only about primes at most 1000; it has no infinite-tail premise. -/
theorem finite_prime_product_le :
    (∏ p ∈ (Finset.range 1001).filter Nat.Prime,
      (1 + ((p : ℝ) ^ ((2 : ℝ) / 5) + (p : ℝ) ^ ((4 : ℝ) / 5)) /
        ((p * (p - 1) : ℕ) : ℝ))) ≤ (223 : ℝ) / 20 := by
  have hsubset : (Finset.range 1001).filter Nat.Prime ⊆ listed.toFinset := by
    intro p hp
    obtain ⟨hrange, hprime⟩ := Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr
      (prime_mem_listed p hprime (by have := Finset.mem_range.mp hrange; omega))
  have hprod := Finset.prod_le_prod_of_subset_of_one_le (f := factor) hsubset
    (fun p _ => factor_nonneg p) (fun p _ _ => factor_one_le p)
  rw [List.prod_toFinset factor listed_nodup] at hprod
  exact hprod.trans listed_product_le

end RamareFiniteConstants
-- END COMPONENT FinitePrimeProduct.lean

-- BEGIN COMPONENT PrimePowerTail.lean
namespace RamareAnalytic


/-- Decreasing nonnegative weights preserve an inequality of all prefix sums. -/
theorem sum_weighted_le_of_prefix_le
    (a b w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    (hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, w i * a i) ≤ ∑ i ∈ Finset.range N, w i * b i := by
  have hparts (c : ℕ → ℝ) :
      (∑ i ∈ Finset.range N, w i * c i) =
      w (N - 1) * (∑ i ∈ Finset.range N, c i) +
        ∑ i ∈ Finset.range (N - 1),
          (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), c j) := by
    have h := Finset.sum_range_by_parts w c N
    simp only [smul_eq_mul] at h
    rw [h, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hparts a, hparts b]
  apply add_le_add (mul_le_mul_of_nonneg_left (hab N) (hw (N - 1)))
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hab (i + 1))
    (sub_nonneg.mpr (hanti (Nat.le_succ i)))

/-- Linear control on shifted prefix sums gives the sharp elementary power-tail constant. -/
theorem shifted_rpow_tail_of_prefix_le
    (a : ℕ → ℝ) (A : ℝ) (m : ℕ) (s : ℝ)
    (hA : 0 ≤ A) (hm : 1 ≤ m) (hs : 1 < s)
    (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * ((m : ℝ) + (N : ℝ))) :
    Summable (fun i : ℕ => a i * ((m + i : ℕ) : ℝ) ^ (-s)) ∧
      (∑' i : ℕ, a i * ((m + i : ℕ) : ℝ) ^ (-s)) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let w : ℕ → ℝ := fun i => ((m + i : ℕ) : ℝ) ^ (-s)
  let b : ℕ → ℝ := fun i => if i = 0 then A * (m : ℝ) else A
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmR
  have hspos : 0 < s := zero_lt_one.trans hs
  have hsmpos : 0 < s - 1 := sub_pos.mpr hs
  have hsm0 : s - 1 ≠ 0 := hsmpos.ne'
  have hb (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), b i) = A * ((m : ℝ) + (N : ℝ)) := by
    simp [b, Finset.sum_range_succ']
    <;> ring
  have hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i := by
    intro N
    cases N with
    | zero => simp
    | succ N => rw [hb]; exact hprefix N
  have hw : ∀ n, 0 ≤ w n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hanti : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · have hmi : 0 < m + i := by omega
      exact_mod_cast hmi
    · exact_mod_cast Nat.add_le_add_left hij m
    · linarith
  have hantiR : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hmpos.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos
  have htail (N : ℕ) :
      (∑ i ∈ Finset.range N, w (i + 1)) ≤ (m : ℝ) ^ (1 - s) / (s - 1) := by
    have heq : (∑ i ∈ Finset.Ico m (m + N), (((i + 1 : ℕ) : ℝ) ^ (-s))) =
        ∑ i ∈ Finset.range N, w (i + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, w, Nat.add_assoc]
    rw [← heq]
    calc
      _ ≤ ∫ x : ℝ in Set.Ioi (m : ℝ), x ^ (-s) := by
        apply (hantiR.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral hint
        intro x hx
        exact Real.rpow_nonneg (hmpos.trans hx).le _
      _ = (m : ℝ) ^ (1 - s) / (s - 1) := by
        rw [integral_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos,
          show -s + 1 = 1 - s by ring]
        have hn : 1 - s ≠ 0 := by linarith
        field_simp
        <;> ring
  have hpower : (m : ℝ) * (m : ℝ) ^ (-s) = (m : ℝ) ^ (1 - s) := by
    rw [show 1 - s = 1 + (-s) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hweighted_b (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * b i) =
        A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := by
    simp [b, Finset.sum_range_succ']
    rw [← Finset.sum_mul]
    ring
  have hfinite (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * a i) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N + 1), w i * b i :=
        sum_weighted_le_of_prefix_le a b w hw hanti hab (N + 1)
      _ = A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := hweighted_b N
      _ ≤ A * ((m : ℝ) * w 0 + (m : ℝ) ^ (1 - s) / (s - 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (htail N)) hA
      _ = _ := by
        simp only [w, Nat.add_zero, hpower]
        field_simp
        <;> ring
  have hnonneg : ∀ i, 0 ≤ w i * a i := fun i => mul_nonneg (hw i) (ha i)
  have hrange : ∀ N, (∑ i ∈ Finset.range N, w i * a i) ≤
      A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ N => exact hfinite N
  have hsum := summable_of_sum_range_le hnonneg hrange
  have hbound := Real.tsum_le_of_sum_range_le hnonneg hrange
  simpa only [w, mul_comm] using And.intro hsum hbound

/-- Chebyshev's theta estimate bounds prime logarithms weighted by p^(-s).
The index m+k enumerates every integer at least m exactly once. -/
theorem prime_power_log_tail (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log (p : ℝ) else 0
  have hc : ∀ n, 0 ≤ c n := by
    intro n
    dsimp only [c]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · exact le_rfl
  have hprefix (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), c (m + i)) ≤ Real.log 4 * ((m : ℝ) + (N : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.Ico m (m + N + 1), c i := by
        rw [Finset.sum_Ico_eq_sum_range,
          show m + N + 1 - m = N + 1 by omega]
      _ ≤ ∑ i ∈ Finset.range (m + N + 1), c i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
        · intro i hi hi'
          exact hc i
      _ = Chebyshev.theta ((m + N : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
          ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
      _ ≤ Real.log 4 * ((m + N : ℕ) : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_add]
  have h := shifted_rpow_tail_of_prefix_le (fun i => c (m + i))
    (Real.log 4) m s (Real.log_nonneg (by norm_num)) hm hs
    (fun i => hc (m + i)) hprefix
  simpa only [c, ite_mul, zero_mul] using h

end RamareAnalytic
-- END COMPONENT PrimePowerTail.lean

-- BEGIN COMPONENT WeightedEulerConstants.lean
namespace RamareWeightedConstants


/-- A rational lower bound from the nonnegative odd-power logarithm series. -/
private def logLower (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private theorem logLower_le (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    (logLower x terms : ℝ) ≤ Real.log (x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hnonneg hlt terms
  rw [hratio] at h
  unfold logLower
  push_cast
  linarith

/-- Range reduction keeps the logarithm-series argument at most one third
when `2^k ≤ N ≤ 2^(k+1)`. Only the lower inequality is needed for soundness. -/
private def logLowerNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logLower 2 terms + logLower ((N : ℚ) / 2 ^ k) terms

private theorem logLowerNat_le (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    (logLowerNat N k terms : ℝ) ≤ Real.log (N : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := logLower_le 2 (by norm_num) terms
  norm_num at htwo
  have hrest := logLower_le ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by
    field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logLowerNat
  push_cast at hrest ⊢
  linarith

private theorem log_thousand_rational_certificate :
    (69 : ℚ) / 10 ≤ logLowerNat 1000 9 9 := by
  decide +kernel

theorem log_thousand_lower : (69 / 10 : ℝ) ≤ Real.log 1000 := by
  have hrat : (69 / 10 : ℝ) ≤ (logLowerNat 1000 9 9 : ℝ) := by
    have hcR := (Rat.cast_le (K := ℝ)).2 log_thousand_rational_certificate
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcR
  exact hrat.trans (by
    simpa only [Nat.cast_ofNat] using logLowerNat_le 1000 9 9 (by decide +kernel))

private theorem log_seven_fifths_rational_certificate :
    (1 : ℚ) / 3 ≤ logLower (7 / 5) 2 := by
  decide +kernel

theorem log_seven_fifths_lower : (1 / 3 : ℝ) ≤ Real.log (7 / 5 : ℝ) := by
  have hrat : (1 / 3 : ℝ) ≤ (logLower (7 / 5) 2 : ℝ) := by
    have hcR := (Rat.cast_le (K := ℝ)).2 log_seven_fifths_rational_certificate
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hcR
  exact hrat.trans (by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      logLower_le (7 / 5) (by norm_num) 2)

theorem thousand_negative_fifth_upper :
    (1000 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (63 / 250 : ℝ) := by
  have hp : 0 ≤ (1000 : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow : ((1000 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = 1000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
    norm_num
  have hbase : (250 / 63 : ℝ) ≤ (1000 : ℝ) ^ (1 / 5 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 250 / 63) hp
      (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hpow]
    norm_num
  have hinv : ((1000 : ℝ) ^ (1 / 5 : ℝ))⁻¹ ≤ (63 / 250 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1000) _)).mpr
    nlinarith [hbase]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1000)]
  exact hinv

end RamareWeightedConstants
-- END COMPONENT WeightedEulerConstants.lean

-- BEGIN COMPONENT WeightedEulerAssembly.lean
namespace RamareAnalytic


noncomputable def weightedEulerIncrement (p : ℕ) : ℝ :=
  ((p : ℝ) ^ (2 / 5 : ℝ) + (p : ℝ) ^ (4 / 5 : ℝ)) /
    ((p * (p - 1) : ℕ) : ℝ)

private noncomputable def weightedIncrementTail (p : ℕ) : ℝ :=
  if 1000 < p ∧ p.Prime then weightedEulerIncrement p else 0

private noncomputable def weightedPowerTail (s : ℝ) (p : ℕ) : ℝ :=
  if 1000 < p ∧ p.Prime then Real.log (p : ℝ) * (p : ℝ) ^ (-s) else 0

/-- The literal checked analytic-component interface; no Euler bound is included. -/
def PrimePowerTailEstimate : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (s : ℝ), 1 < s →
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s)

private theorem weightedEulerIncrement_nonneg (p : ℕ) :
    0 ≤ weightedEulerIncrement p := by
  exact div_nonneg
    (add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (Real.rpow_nonneg (Nat.cast_nonneg p) _)) (Nat.cast_nonneg _)

private theorem weightedIncrementTail_nonneg (p : ℕ) :
    0 ≤ weightedIncrementTail p := by
  unfold weightedIncrementTail
  split_ifs
  · exact weightedEulerIncrement_nonneg p
  · exact le_rfl

private theorem weightedPowerTail_nonneg (s : ℝ) (p : ℕ) :
    0 ≤ weightedPowerTail s p := by
  unfold weightedPowerTail
  split_ifs with hp
  · exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le))
      (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  · exact le_rfl

private theorem power_tail_unshifted (hpower : PrimePowerTailEstimate)
    (s : ℝ) (hs : 1 < s) :
    Summable (weightedPowerTail s) ∧
      (∑' p : ℕ, weightedPowerTail s p) ≤
        Real.log 4 * (s / (s - 1)) * (1001 : ℝ) ^ (1 - s) := by
  have h := hpower 1001 (by norm_num) s hs
  have heq : (fun k : ℕ => weightedPowerTail s (k + 1001)) =
      (fun k : ℕ => if (1001 + k).Prime then
        Real.log ((1001 + k : ℕ) : ℝ) * ((1001 + k : ℕ) : ℝ) ^ (-s) else 0) := by
    funext k
    have hk : 1000 < k + 1001 := by omega
    have hk' : 1000 < 1001 + k := by omega
    simp only [weightedPowerTail, hk, hk', true_and, Nat.add_comm k 1001]
  have hshift : Summable (fun k : ℕ => weightedPowerTail s (k + 1001)) := by
    rw [heq]
    exact h.1
  have hglobal := (summable_nat_add_iff 1001).mp hshift
  have hzero : (∑ p ∈ Finset.range 1001, weightedPowerTail s p) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hn : ¬1000 < p := by have := Finset.mem_range.mp hp; omega
    simp [weightedPowerTail, hn]
  have hsum := hglobal.sum_add_tsum_nat_add 1001
  rw [hzero, zero_add, heq] at hsum
  exact ⟨hglobal, hsum ▸ h.2⟩

private theorem increment_le_log_power_majorant
    (hlog1000 : (69 / 10 : ℝ) ≤ Real.log 1000)
    (p : ℕ) (hp : 1000 < p) :
    weightedEulerIncrement p ≤
      ((1000 / 999 : ℝ) * (10 / 69 : ℝ)) *
        (Real.log (p : ℝ) * (p : ℝ) ^ (-(8 / 5 : ℝ)) +
          Real.log (p : ℝ) * (p : ℝ) ^ (-(6 / 5 : ℝ))) := by
  have hpR : (1000 : ℝ) < p := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hpm : 0 < (p : ℝ) - 1 := by linarith
  have hden : 0 < (p : ℝ) * ((p : ℝ) - 1) := mul_pos hp0 hpm
  have hcast : ((p * (p - 1) : ℕ) : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ p), Nat.cast_one]
  have hrecip : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      (1000 / 999 : ℝ) / (p : ℝ) ^ (2 : ℕ) := by
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hp0)).mpr
    have hq : 0 ≤ (p : ℝ) * ((p : ℝ) - 1000) :=
      mul_nonneg hp0.le (by linarith)
    nlinarith
  have hpow : weightedEulerIncrement p ≤ (1000 / 999 : ℝ) *
      ((p : ℝ) ^ (-(8 / 5 : ℝ)) + (p : ℝ) ^ (-(6 / 5 : ℝ))) := by
    unfold weightedEulerIncrement
    rw [hcast, div_eq_mul_one_div]
    calc
      _ ≤ ((p : ℝ) ^ (2 / 5 : ℝ) + (p : ℝ) ^ (4 / 5 : ℝ)) *
          ((1000 / 999 : ℝ) / (p : ℝ) ^ (2 : ℕ)) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = _ := by
        rw [show -(8 / 5 : ℝ) = (2 / 5 : ℝ) - 2 by norm_num,
          show -(6 / 5 : ℝ) = (4 / 5 : ℝ) - 2 by norm_num,
          Real.rpow_sub hp0, Real.rpow_sub hp0, Real.rpow_two]
        ring
  have hlog : (69 / 10 : ℝ) ≤ Real.log (p : ℝ) :=
    hlog1000.trans (Real.log_le_log (by norm_num) hpR.le)
  have hone : (1 : ℝ) ≤ (10 / 69 : ℝ) * Real.log (p : ℝ) := by linarith
  have hnonneg : 0 ≤ (p : ℝ) ^ (-(8 / 5 : ℝ)) + (p : ℝ) ^ (-(6 / 5 : ℝ)) :=
    add_nonneg (Real.rpow_nonneg hp0.le _) (Real.rpow_nonneg hp0.le _)
  calc
    _ ≤ _ := hpow
    _ ≤ (1000 / 999 : ℝ) * (((10 / 69 : ℝ) * Real.log (p : ℝ)) *
        ((p : ℝ) ^ (-(8 / 5 : ℝ)) + (p : ℝ) ^ (-(6 / 5 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hnonneg
    _ = _ := by ring

/-- Derives the Euler-increment tail bound from two power tails and finite real certificates. -/
theorem weighted_increment_tail_le
    (hpower : PrimePowerTailEstimate)
    (hlog4 : Real.log 4 ≤ (7 / 5 : ℝ))
    (hlog1000 : (69 / 10 : ℝ) ≤ Real.log 1000)
    (hroot : (1000 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (63 / 250 : ℝ)) :
    Summable weightedIncrementTail ∧ (∑' p : ℕ, weightedIncrementTail p) ≤ (1 / 3 : ℝ) := by
  have h8 := power_tail_unshifted hpower (8 / 5 : ℝ) (by norm_num)
  have h6 := power_tail_unshifted hpower (6 / 5 : ℝ) (by norm_num)
  have hroot1 : (1001 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (63 / 250 : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1000)
      (by norm_num : (1000 : ℝ) ≤ 1001) (by norm_num)).trans hroot
  have hcube : ((1001 : ℝ) ^ (-(1 / 5 : ℝ))) ^ (3 : ℕ) =
      (1001 : ℝ) ^ (-(3 / 5 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1001)]
    norm_num
  have hroot3 : (1001 : ℝ) ^ (-(3 / 5 : ℝ)) ≤ (63 / 250 : ℝ) ^ (3 : ℕ) := by
    rw [← hcube]
    exact (pow_le_pow_iff_left₀ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1001) _)
      (by norm_num : (0 : ℝ) ≤ 63 / 250) (by norm_num : (3 : ℕ) ≠ 0)).mpr hroot1
  have hb8 : (∑' p : ℕ, weightedPowerTail (8 / 5 : ℝ) p) ≤
      (7 / 5 : ℝ) * (8 / 3 : ℝ) * (63 / 250 : ℝ) ^ (3 : ℕ) := by
    calc
      _ ≤ Real.log 4 * (8 / 3 : ℝ) * (1001 : ℝ) ^ (-(3 / 5 : ℝ)) := by
        convert h8.2 using 1 <;> norm_num
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hlog4 (by norm_num)) hroot3
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1001) _) (by norm_num)
  have hb6 : (∑' p : ℕ, weightedPowerTail (6 / 5 : ℝ) p) ≤
      (7 / 5 : ℝ) * 6 * (63 / 250 : ℝ) := by
    calc
      _ ≤ Real.log 4 * 6 * (1001 : ℝ) ^ (-(1 / 5 : ℝ)) := by
        convert h6.2 using 1 <;> norm_num
      _ ≤ _ := mul_le_mul
        (mul_le_mul_of_nonneg_right hlog4 (by norm_num)) hroot1
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1001) _) (by norm_num)
  let K : ℝ := (1000 / 999 : ℝ) * (10 / 69 : ℝ)
  have hK : 0 ≤ K := by norm_num [K]
  have hmajor : ∀ p : ℕ, weightedIncrementTail p ≤
      K * (weightedPowerTail (8 / 5 : ℝ) p + weightedPowerTail (6 / 5 : ℝ) p) := by
    intro p
    by_cases hp : 1000 < p ∧ p.Prime
    · simpa [weightedIncrementTail, weightedPowerTail, hp, K] using
        increment_le_log_power_majorant hlog1000 p hp.1
    · simp [weightedIncrementTail, weightedPowerTail, hp]
  have hG := (h8.1.add h6.1).mul_left K
  have hV := Summable.of_nonneg_of_le weightedIncrementTail_nonneg hmajor hG
  have hGsum := (h8.1.hasSum.add h6.1.hasSum).mul_left K
  refine ⟨hV, ?_⟩
  calc
    _ ≤ ∑' p : ℕ, K * (weightedPowerTail (8 / 5 : ℝ) p +
        weightedPowerTail (6 / 5 : ℝ) p) :=
      Summable.tsum_le_tsum hmajor hV hG
    _ = K * ((∑' p : ℕ, weightedPowerTail (8 / 5 : ℝ) p) +
        (∑' p : ℕ, weightedPowerTail (6 / 5 : ℝ) p)) := hGsum.tsum_eq
    _ ≤ K * ((7 / 5 : ℝ) * (8 / 3 : ℝ) * (63 / 250 : ℝ) ^ (3 : ℕ) +
        (7 / 5 : ℝ) * 6 * (63 / 250 : ℝ)) :=
      mul_le_mul_of_nonneg_left (add_le_add hb8 hb6) hK
    _ ≤ (1 / 3 : ℝ) := by norm_num [K]

/-- Exact quantitative Euler-limit assembly. The limit premise contains no bound. -/
theorem weighted_euler_limit_le_sixteen
    (hpower : PrimePowerTailEstimate)
    (hfinite : (∏ p ∈ (Finset.range 1001).filter Nat.Prime,
      (1 + ((p : ℝ) ^ (2 / 5 : ℝ) + (p : ℝ) ^ (4 / 5 : ℝ)) /
        ((p * (p - 1) : ℕ) : ℝ))) ≤ (223 / 20 : ℝ))
    (hlog4 : Real.log 4 ≤ (7 / 5 : ℝ))
    (hlog1000 : (69 / 10 : ℝ) ≤ Real.log 1000)
    (hroot : (1000 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (63 / 250 : ℝ))
    (hlogSevenFifths : (1 / 3 : ℝ) ≤ Real.log (7 / 5 : ℝ))
    (W : ℝ)
    (hEuler : Tendsto (fun N : ℕ =>
      ∏ p ∈ Nat.primesBelow N, (1 + weightedEulerIncrement p)) atTop (𝓝 W)) :
    W ≤ 16 := by
  classical
  have ht := weighted_increment_tail_le hpower hlog4 hlog1000 hroot
  have hfactor0 (p : ℕ) : 0 ≤ 1 + weightedEulerIncrement p :=
    add_nonneg zero_le_one (weightedEulerIncrement_nonneg p)
  have hfactor1 (p : ℕ) : 1 ≤ 1 + weightedEulerIncrement p :=
    le_add_of_nonneg_right (weightedEulerIncrement_nonneg p)
  have hexp : Real.exp (1 / 3 : ℝ) ≤ (7 / 5 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).mp hlogSevenFifths
  apply le_of_tendsto' hEuler
  intro N
  let S := Nat.primesBelow N
  let L := S.filter (fun p => p < 1001)
  let H := S.filter (fun p => ¬p < 1001)
  have hlow : (∏ p ∈ L, (1 + weightedEulerIncrement p)) ≤ (223 / 20 : ℝ) := by
    have hsub : L ⊆ (Finset.range 1001).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hcut⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcut,
        (Nat.mem_primesBelow.mp hpS).2⟩
    have hprod := Finset.prod_le_prod_of_subset_of_one_le
      (f := fun p => 1 + weightedEulerIncrement p) hsub
      (fun p hp => hfactor0 p) (fun p hp hp' => hfactor1 p)
    exact hprod.trans hfinite
  have hsum : (∑ p ∈ H, weightedEulerIncrement p) ≤ (1 / 3 : ℝ) := by
    have heq : (∑ p ∈ H, weightedEulerIncrement p) =
        ∑ p ∈ H, weightedIncrementTail p := by
      apply Finset.sum_congr rfl
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hcut⟩
      have hpprime : p.Prime := (Nat.mem_primesBelow.mp hpS).2
      have hpgt : 1000 < p := by omega
      simp [weightedIncrementTail, hpgt, hpprime]
    rw [heq]
    exact (ht.1.sum_le_tsum H (fun p hp => weightedIncrementTail_nonneg p)).trans ht.2
  have hhigh : (∏ p ∈ H, (1 + weightedEulerIncrement p)) ≤ (7 / 5 : ℝ) :=
    (Real.prod_one_add_le_exp_sum H weightedEulerIncrement_nonneg).trans
      ((Real.exp_le_exp.mpr hsum).trans hexp)
  calc
    _ = (∏ p ∈ L, (1 + weightedEulerIncrement p)) *
        (∏ p ∈ H, (1 + weightedEulerIncrement p)) :=
      (Finset.prod_filter_mul_prod_filter_not S (fun p => p < 1001)
        (fun p => 1 + weightedEulerIncrement p)).symm
    _ ≤ (223 / 20 : ℝ) * (7 / 5 : ℝ) :=
      mul_le_mul hlow hhigh (Finset.prod_nonneg (fun p hp => hfactor0 p)) (by norm_num)
    _ ≤ 16 := by norm_num

end RamareAnalytic
-- END COMPONENT WeightedEulerAssembly.lean

-- BEGIN COMPONENT WeightedEulerLimit.lean
namespace RamareAnalytic



private theorem weighted_prime_factor
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, |h (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ (2 / 5 : ℝ)) =
      1 + weightedEulerIncrement p := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)
  change (∑' k : ℕ, f (p ^ k)) = _
  have hz : ∀ k : ℕ, 3 ≤ k → f (p ^ k) = 0 := by
    intro k hk
    simp only [f, hpz p k hp hk, abs_zero, zero_mul]
  have hthree : (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) := by
    rw [tsum_eq_sum (s := Finset.range 3) (by
      intro k hk
      apply hz k
      simpa only [Finset.mem_range, not_lt] using hk)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hcoef : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
    div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (by linarith))
  have hsquare : ((p ^ 2 : ℕ) : ℝ) ^ (2 / 5 : ℝ) =
      (p : ℝ) ^ (4 / 5 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    norm_num
  have hform : f 1 + f p + f (p ^ 2) =
      1 + ((p : ℝ) ^ (2 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
        (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    simp only [f, hmul.1, (hpv p hp).1, (hpv p hp).2, Nat.cast_one,
      Real.one_rpow, abs_one, one_mul, abs_neg, abs_of_nonneg hcoef, hsquare]
    ring
  rw [hthree, hform]
  unfold weightedEulerIncrement
  rw [Nat.cast_mul, Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  ring

/-- The actual finite Euler products converge to the weighted absolute
coefficient moment. The qualitative summability premise is supplied by the
separate prime-power convergence theorem; no numerical moment bound is used. -/
theorem weighted_euler_limit_of_summable
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (hweighted : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) :
    Tendsto (fun N : ℕ =>
      ∏ p ∈ Nat.primesBelow N, (1 + weightedEulerIncrement p)) atTop
      (𝓝 (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, hmul.1]
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hf_mul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f, hmul.2 hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hfSum : Summable f := hweighted
  have hfNorm : Summable (fun n : ℕ => ‖f n‖) :=
    hfSum.congr (fun n => (Real.norm_of_nonneg (hf_nonneg n)).symm)
  have hEuler := EulerProduct.eulerProduct hf1 hf_mul hfNorm hf0
  have hproducts : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k)) =
      (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 + weightedEulerIncrement p)) := by
    funext N
    apply Finset.prod_congr rfl
    intro p hp
    exact weighted_prime_factor h hmul hpv hpz p (Nat.mem_primesBelow.mp hp).2
  rw [hproducts] at hEuler
  exact hEuler

end RamareAnalytic
-- END COMPONENT WeightedEulerLimit.lean

-- BEGIN LOG4 EXTRACT
namespace RamareFiniteConstants

private def logSeries (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private def logUpper (x : ℚ) (terms : ℕ) : ℚ :=
  logSeries x terms +
    2 * ((x - 1) / (x + 1)) ^ (2 * terms + 1) /
      (1 - ((x - 1) / (x + 1)) ^ 2)

private theorem log_le_upper (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    Real.log (x : ℝ) ≤ (logUpper x terms : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.log_div_le_sum_range_add hnonneg hlt terms
  rw [hratio] at h
  calc
    Real.log (x : ℝ) = 2 * ((1 / 2 : ℝ) * Real.log (x : ℝ)) := by ring
    _ ≤ 2 * ((∑ i ∈ Finset.range terms,
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ (2 * i + 1) / (2 * (i : ℝ) + 1)) +
        (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ (2 * terms + 1) /
          (1 - (((x : ℝ) - 1) / ((x : ℝ) + 1)) ^ 2)) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = (logUpper x terms : ℝ) := by
      unfold logUpper logSeries
      push_cast
      ring

private def logUpperNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logUpper 2 terms + logUpper ((N : ℚ) / 2 ^ k) terms

private theorem log_le_upperNat (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    Real.log (N : ℝ) ≤ (logUpperNat N k terms : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := log_le_upper 2 (by norm_num) terms
  norm_num at htwo
  have hrest := log_le_upper ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logUpperNat
  push_cast at hrest ⊢
  linarith

theorem log_four_le : Real.log 4 ≤ (7 : ℝ) / 5 := by
  have h := log_le_upperNat 4 2 9 (by decide +kernel)
  have hc : logUpperNat 4 2 9 ≤ (7 : ℚ) / 5 := by decide +kernel
  have hcr : (logUpperNat 4 2 9 : ℝ) ≤ (7 : ℝ) / 5 := by
    have hcR := (Rat.cast_le (K := ℝ)).2 hc
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcR
  simpa only [Nat.cast_ofNat] using h.trans hcr

end RamareFiniteConstants
-- END LOG4 EXTRACT

theorem solution
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ≤ 16 := by
  have hweighted := RamareAnalytic.weighted_summable_of_prime_power_values h hmul hpv hpz
  have hlimit := RamareAnalytic.weighted_euler_limit_of_summable h hmul hpv hpz hweighted
  have hpower : RamareAnalytic.PrimePowerTailEstimate := by
    unfold RamareAnalytic.PrimePowerTailEstimate
    intro m hm s hs
    exact RamareAnalytic.prime_power_log_tail m hm s hs
  exact RamareAnalytic.weighted_euler_limit_le_sixteen
    hpower
    RamareFiniteConstants.finite_prime_product_le
    RamareFiniteConstants.log_four_le
    RamareWeightedConstants.log_thousand_lower
    RamareWeightedConstants.thousand_negative_fifth_upper
    RamareWeightedConstants.log_seven_fifths_lower
    (∑' n : ℕ, |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) hlimit

#print axioms solution
