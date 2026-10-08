-- Prove2me | solution 1 for PrimePairSieve.prime_second_logarithmic_moment_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T15:17:38.542995+00:00
-- url     : https://prove2.me/submissions/252965ea-4374-443f-a150-d76373856748

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

open scoped BigOperators
open Set MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

namespace PrimeMomentCertificate
noncomputable section

private def binaryBin (n : ℕ) : ℕ := if n < 2 then 0 else if n < 4 then 1 else if n < 8 then 2 else if n < 16 then 3 else if n < 32 then 4 else if n < 64 then 5 else if n < 128 then 6 else if n < 256 then 7 else if n < 512 then 8 else if n < 1024 then 9 else if n < 2048 then 10 else 11

private lemma bin_power_le (n : ℕ) (hn : 0<n) : 2^binaryBin n ≤ n := by
  unfold binaryBin
  split_ifs <;> norm_num <;> omega

private def logUpper (n : ℕ) : ℚ :=
  let k := binaryBin n
  let y : ℚ := ((n : ℚ) - 2 ^ k) / ((n : ℚ) + 2 ^ k)
  (k : ℚ) * (6931471808 / 10^10) +
    2 * ((∑ i ∈ Finset.range 2, y^(2*i+1) / (2*i+1 : ℕ)) + y^5/(1-y^2))

private theorem log_le_logUpper (n : ℕ) (hn : 0 < n) : Real.log n ≤ (logUpper n : ℝ) := by
  let k := binaryBin n
  let y : ℝ := ((n : ℝ) - 2 ^ k) / ((n : ℝ) + 2 ^ k)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : (2 : ℝ)^k ≤ n := by exact_mod_cast bin_power_le n hn
  have hp : (0 : ℝ) < (2 : ℝ)^k := by positivity
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hk) (by positivity)
  have hy1 : y < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  have heq : (1+y)/(1-y) = (n : ℝ)/2^k := by dsimp [y]; field_simp; ring
  have h := Real.log_div_le_sum_range_add hy0 hy1 2
  rw [heq, Real.log_div hnR.ne' hp.ne', Real.log_pow] at h
  have h2 : Real.log 2 ≤ (6931471808 / 10^10 : ℝ) := by
    have h := Real.log_two_lt_d9.le
    norm_num at h ⊢
    exact h
  have hc : (logUpper n : ℝ) =
      (k : ℝ)*(6931471808/10^10 : ℝ) +
        2*((∑ i ∈ Finset.range 2, y^(2*i+1)/(2*i+1 : ℕ)) + y^5/(1-y^2)) := by
    dsimp [logUpper, k, y]
    push_cast
    rfl
  rw [hc]
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg k)
  push_cast at h ⊢
  norm_num at h
  linarith

private def kernel (x : ℝ) := Real.log x^2 / x^2
private def potential (x : ℝ) := (Real.log x^2 + 2*Real.log x + 2)/x

private lemma kernel_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt kernel ((2*Real.log x-2*Real.log x^2)/x^3) x := by
  have h := ((Real.hasDerivAt_log hx.ne').pow 2).div
    ((hasDerivAt_id' x).pow 2) (pow_ne_zero 2 hx.ne')
  convert! h using 1 <;> (try simp [kernel]) <;> field_simp [hx.ne'] <;> ring

private lemma potential_deriv (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t => -potential t) (kernel x) x := by
  have h := (((((Real.hasDerivAt_log hx.ne').pow 2).add
    ((Real.hasDerivAt_log hx.ne').const_mul 2)).add (hasDerivAt_const x (2 : ℝ))).div
    (hasDerivAt_id' x) hx.ne').neg
  convert! h using 1 <;> (try simp [kernel, potential]) <;> field_simp [hx.ne'] <;> ring

private lemma log_ge_one (x : ℝ) (hx : 4 ≤ x) : 1 ≤ Real.log x := by
  have h := Real.strictMonoOn_log.monotoneOn (by norm_num : (4:ℝ) ∈ Ioi 0)
    (show x ∈ Ioi 0 by change 0 < x; linarith) hx
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4] at h
  linarith [Real.log_two_gt_d9]

private lemma kernel_antitone : AntitoneOn kernel (Ici 4) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 4)
    (fun x hx => (kernel_deriv x (by change 4 ≤ x at hx; linarith)).continuousAt.continuousWithinAt)
    (fun x hx => (kernel_deriv x (by
      have h : 4 < x := by simpa using hx
      linarith)).hasDerivWithinAt)
  intro x hx
  have hx4 : 4 ≤ x := (interior_subset hx)
  have hl := log_ge_one x hx4
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith
  · positivity

private lemma kernel_tail (N M : ℕ) (hN : 4 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Ico N M, kernel (n+1)) ≤ potential N := by
  have hN4 : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hM4 : (4 : ℝ) ≤ M := by exact_mod_cast hN.trans hNM
  have anti : AntitoneOn kernel (Icc (N : ℝ) M) :=
    kernel_antitone.mono (fun x hx => hN4.trans hx.1)
  have hsum := anti.sum_le_integral_Ico hNM
  have hi : AntitoneOn kernel (uIcc (N:ℝ) M) := by
    rw [uIcc_of_le (show (N:ℝ) ≤ M by exact_mod_cast hNM)]
    exact anti
  have hInt : (∫ x in (N:ℝ)..M, kernel x) = potential N - potential M := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (show (N:ℝ) ≤ M by exact_mod_cast hNM)
      (fun x hx => (potential_deriv x (by linarith [hx.1])).continuousAt.continuousWithinAt)
      (fun x hx => potential_deriv x (by linarith [hx.1])) hi.intervalIntegrable
    simpa only [sub_eq_add_neg, neg_neg, add_comm] using h
  rw [hInt] at hsum
  push_cast at hsum
  have hV : 0 ≤ potential M := by
    unfold potential
    have := (log_ge_one M hM4)
    positivity
  linarith

private def rationalUpper (n : ℕ) : ℚ :=
  (8*(n:ℚ)^2-10*n+4)/((n:ℚ)^2*((n:ℚ)-1)^2)*(logUpper n)^2

-- Upward-rounded exact chunk totals; each inequality is checked by norm_num.
private def chunkBound (b : ℕ) : ℚ :=
  (([726273043, 20667853, 6266928, 3633277, 2535882, 1467354, 1295270, 881127, 761512, 583578, 562045, 362254, 390441, 254045, 340310, 214585, 243558, 174754, 158676, 156690] : List ℕ).getD b 0 : ℚ)/10^8

private lemma chunk_numeric (b : ℕ) (hb : b < 20) :
    (∑ n ∈ Finset.range 100, if Nat.Prime (100*b+n) then rationalUpper (100*b+n) else 0) ≤
      chunkBound b := by
  interval_cases b
  all_goals
    norm_num only [Finset.sum_range_succ]
    simp only [if_true, if_false, add_zero, zero_add]
    norm_num [rationalUpper, logUpper, chunkBound, binaryBin]

private lemma sum_blocks (f : ℕ → ℚ) (N : ℕ) :
    (∑ n ∈ Finset.range (100*N), f n) =
      ∑ b ∈ Finset.range N, ∑ n ∈ Finset.range 100, f (100*b+n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    rw [Finset.sum_range_succ (f := fun b => ∑ n ∈ Finset.range 100, f (100*b+n))]

private lemma prefix_numeric :
    (∑ n ∈ (Finset.range 2001).filter Nat.Prime, rationalUpper n) ≤ (769/100:ℚ) := by
  rw [Finset.sum_filter, Finset.sum_range_succ]
  simp only [show ¬Nat.Prime 2000 by norm_num, if_false, add_zero]
  rw [show 2000=100*20 by rfl, sum_blocks]
  calc
    _ ≤ ∑ b ∈ Finset.range 20, chunkBound b :=
      Finset.sum_le_sum (fun b hb => chunk_numeric b (Finset.mem_range.mp hb))
    _ ≤ 769/100 := by decide +kernel

private noncomputable def primeTerm (n : ℕ) : ℝ :=
  if Nat.Prime n then (8*(n:ℝ)^2-10*n+4)/((n:ℝ)^2*((n:ℝ)-1)^2)*Real.log n^2 else 0

private lemma coefficient_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ (8*(n:ℝ)^2-10*n+4)/((n:ℝ)^2*((n:ℝ)-1)^2) := by
  have hnR : (2:ℝ) ≤ n := by exact_mod_cast hn
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg ((n:ℝ)-1)]

private lemma primeTerm_nonneg (n : ℕ) : 0 ≤ primeTerm n := by
  unfold primeTerm
  split_ifs with h
  · exact mul_nonneg (coefficient_nonneg n h.two_le) (sq_nonneg _)
  · exact le_rfl

private lemma primeTerm_le_rational (n : ℕ) (hn : Nat.Prime n) :
    primeTerm n ≤ (rationalUpper n : ℝ) := by
  rw [primeTerm, if_pos hn]
  have hl0 : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn.one_lt.le)
  have hl := log_le_logUpper n hn.pos
  have hcoeff := coefficient_nonneg n hn.two_le
  have hq : (8*(n:ℝ)^2-10*n+4)/((n:ℝ)^2*((n:ℝ)-1)^2)*Real.log n^2 ≤
      ((8*(n:ℚ)^2-10*n+4)/((n:ℚ)^2*((n:ℚ)-1)^2)*(logUpper n)^2 : ℚ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl 2) hcoeff
  exact hq

private lemma prime_prefix : (∑ n ∈ Finset.range 2001, primeTerm n) ≤ (769/100:ℝ) := by
  have heq : (∑ n ∈ Finset.range 2001, primeTerm n) =
      ∑ n ∈ (Finset.range 2001).filter Nat.Prime, primeTerm n := by
    simp only [Finset.sum_filter, primeTerm]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> rfl
  rw [heq]
  calc
    _ ≤ ∑ n ∈ (Finset.range 2001).filter Nat.Prime, (rationalUpper n : ℝ) :=
      Finset.sum_le_sum (fun n hn => primeTerm_le_rational n (Finset.mem_filter.mp hn).2)
    _ ≤ 769/100 := by
      have hr : ((∑ n ∈ (Finset.range 2001).filter Nat.Prime, rationalUpper n : ℚ):ℝ) ≤
          ((769/100:ℚ):ℝ) := Rat.cast_le.mpr prefix_numeric
      simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_ofNat] using hr

private lemma primeTerm_tail (n : ℕ) (hn : 2001 ≤ n) :
    primeTerm n ≤ (8*(2001/2000:ℝ)^2)*kernel n := by
  have hnR : (2001:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0:ℝ)<n := by linarith
  have hn1 : (0:ℝ)<(n:ℝ)-1 := by linarith
  have hrat : (n:ℝ)/((n:ℝ)-1) ≤ 2001/2000 := by
    apply (div_le_iff₀ hn1).mpr
    linarith
  have hcoeff : (8*(n:ℝ)^2-10*n+4)/((n:ℝ)^2*((n:ℝ)-1)^2) ≤
      8*(2001/2000:ℝ)^2/(n:ℝ)^2 := by
    calc
      _ ≤ 8*(n:ℝ)^2/((n:ℝ)^2*((n:ℝ)-1)^2) :=
        div_le_div_of_nonneg_right (by linarith) (by positivity)
      _ = 8*((n:ℝ)/((n:ℝ)-1))^2/(n:ℝ)^2 := by field_simp <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrat 2) (by norm_num))
        (by positivity)
  unfold primeTerm
  split_ifs
  · simpa only [kernel, div_mul_eq_mul_div, mul_div_assoc, mul_assoc] using
      mul_le_mul_of_nonneg_right hcoeff (sq_nonneg (Real.log (n:ℝ)))
  · unfold kernel
    positivity

private lemma numerical_tail : (8*(2001/2000:ℝ)^2)*potential 2000 ≤ 31/100 := by
  have hl : Real.log 2000 ≤ (77/10:ℝ) := by
    have h := log_le_logUpper 2000 (by norm_num)
    have hv : logUpper 2000 ≤ (77/10:ℚ) := by decide +kernel
    have hr : (logUpper 2000 : ℝ) ≤ ((77/10:ℚ):ℝ) := Rat.cast_le.mpr hv
    norm_num at hr
    exact h.trans hr
  have hl0 := (log_ge_one 2000 (by norm_num))
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log 2000) hl 2
  unfold potential
  nlinarith

private lemma shift_sum (N M : ℕ) (hNM : N+1 ≤ M) :
    (∑ n ∈ Finset.Ico (N+1) M, kernel n) =
      ∑ n ∈ Finset.Ico N (M-1), kernel (n+1) := by
  have hc : M-1+1=M := by omega
  simpa only [hc, Nat.cast_add, Nat.cast_one] using
    (Finset.sum_Ico_add' (fun n : ℕ => kernel n) N (M-1) (c:=1)).symm

private lemma range_bound (M : ℕ) : (∑ n ∈ Finset.range M, primeTerm n) ≤ 8 := by
  by_cases hM : M ≤ 2001
  · have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM)
      (fun n _ _ => primeTerm_nonneg n)
    linarith [hle, prime_prefix]
  · have hM' : 2001 ≤ M := by omega
    have htail : (∑ n ∈ Finset.Ico 2001 M, primeTerm n) ≤ 31/100 := by
      calc
        _ ≤ ∑ n ∈ Finset.Ico 2001 M, (8*(2001/2000:ℝ)^2)*kernel n :=
          Finset.sum_le_sum (fun n hn => primeTerm_tail n (Finset.mem_Ico.mp hn).1)
        _ = (8*(2001/2000:ℝ)^2)*(∑ n ∈ Finset.Ico 2001 M, kernel n) :=
          (Finset.mul_sum ..).symm
        _ ≤ (8*(2001/2000:ℝ)^2)*potential 2000 := by
          rw [shift_sum 2000 M (by omega)]
          exact mul_le_mul_of_nonneg_left
            (kernel_tail 2000 (M-1) (by norm_num) (by omega)) (by positivity)
        _ ≤ 31/100 := numerical_tail
    rw [← Finset.sum_range_add_sum_Ico primeTerm hM']
    linarith [prime_prefix]

theorem total_bound : (∑' n : ℕ, primeTerm n) ≤ 8 :=
  Real.tsum_le_of_sum_range_le primeTerm_nonneg range_bound

end
end PrimeMomentCertificate


theorem solution :
    (∑' p : Nat.Primes,
      (8*(p:ℝ)^2-10*(p:ℝ)+4)/((p:ℝ)^2*((p:ℝ)-1)^2)*Real.log (p:ℝ)^2) ≤ 8 := by
  have h := PrimeMomentCertificate.total_bound
  have heq : (∑' n : ℕ, PrimeMomentCertificate.primeTerm n) =
      ∑' p : Nat.Primes,
        (8*(p:ℝ)^2-10*(p:ℝ)+4)/((p:ℝ)^2*((p:ℝ)-1)^2)*Real.log (p:ℝ)^2 := by
    let f : ℕ → ℝ := fun n => (8*(n:ℝ)^2-10*n+4)/((n:ℝ)^2*((n:ℝ)-1)^2)*Real.log n^2
    have hs := tsum_subtype (s := {n | Nat.Prime n}) (f := f)
    change (∑' n : ℕ, PrimeMomentCertificate.primeTerm n) =
      ∑' p : {n | Nat.Prime n}, f p
    rw [hs]
    apply tsum_congr
    intro n
    simp [PrimeMomentCertificate.primeTerm, f, Set.indicator_apply]
  rwa [heq] at h

#print axioms solution
