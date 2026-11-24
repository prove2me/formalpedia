-- Prove2me | solution 1 for PrimePairSieve.reciprocal_base_denominator_interval_certificate
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T15:03:06.576986+00:00
-- url     : https://prove2.me/submissions/e3dbf099-812f-4ae5-8f0e-3033133453a7

import Mathlib
import Theorems.Thm_PrimePairSieve_sieve_constants_certificate

open scoped BigOperators
set_option autoImplicit false

namespace ReciprocalFiniteWindow
noncomputable section

def denominator (c : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊z⌋₊, c n / (1 + (n : ℝ) / z)

def correction (z : ℝ) : ℝ := (z+1)/(16*z^2)

lemma denominator_mono (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    denominator c x ≤ denominator c y := by
  have hy : 0 < y := hx.trans_le hxy
  unfold denominator
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, c n / (1 + (n : ℝ) / y) := by
      apply Finset.sum_le_sum
      intro n hn
      have hf : (n : ℝ)/y ≤ (n : ℝ)/x :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx hxy
      exact div_le_div_of_nonneg_left (hc n) (by positivity) (by linarith)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl (Nat.floor_mono hxy))
      (fun n _ _ => div_nonneg (hc n) (by positivity))

lemma correction_antitone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    correction y ≤ correction x := by
  have hy : 0 < y := hx.trans_le hxy
  have hi : 1/y ≤ (1:ℝ)/x := div_le_div_of_nonneg_left (by norm_num) hx hxy
  have hs : 1/y^2 ≤ (1:ℝ)/x^2 := div_le_div_of_nonneg_left
    (by norm_num) (by positivity) (pow_le_pow_left₀ hx.le hxy 2)
  have heq (t : ℝ) (ht : 0 < t) : correction t = (1/t+1/t^2)/16 := by
    unfold correction
    field_simp
    <;> ring
  rw [heq x hx, heq y hy]
  linarith

/-- A rational endpoint certificate controls the entire real interval. -/
theorem interval_certificate (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (C L U ell z : ℝ) (hC : 5/4 ≤ C) (hL : 40 ≤ L)
    (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4*U) ≤ ell)
    (hpositive : correction L * (ell^2/(5/2)) < 1)
    (hcertificate : ell^2/(5/2)/(1-correction L*(ell^2/(5/2))) ≤ denominator c L) :
    Real.log (4*z)^2/(2*C)/(1-correction z*(Real.log (4*z)^2/(2*C))) ≤
      denominator c z := by
  have hLp : 0 < L := by linarith
  have hzp : 0 < z := hLp.trans_le hLz
  have hUp : 0 < U := hzp.trans_le hzU
  have hCp : 0 < C := by linarith
  have hl0 : 0 ≤ Real.log (4*z) := Real.log_nonneg (by linarith)
  have hlU : Real.log (4*z) ≤ Real.log (4*U) :=
    Real.strictMonoOn_log.monotoneOn (by change 0 < 4*z; positivity)
      (by change 0 < 4*U; positivity) (by linarith)
  have hq : Real.log (4*z)^2/(2*C) ≤ ell^2/(5/2) := by
    calc
      _ ≤ ell^2/(2*C) := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hl0 (hlU.trans hlog) 2) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg ell) (by norm_num) (by linarith)
  have hg : correction z ≤ correction L := correction_antitone hLp hLz
  have hg0 : 0 ≤ correction z := by unfold correction; positivity
  have hq0 : 0 ≤ Real.log (4*z)^2/(2*C) := by positivity
  have hgq : correction z*(Real.log (4*z)^2/(2*C)) ≤
      correction L*(ell^2/(5/2)) := mul_le_mul hg hq hq0 (by unfold correction; positivity)
  have hd : 0 < 1-correction L*(ell^2/(5/2)) := by linarith
  calc
    _ ≤ (ell^2/(5/2))/(1-correction z*(Real.log (4*z)^2/(2*C))) :=
      div_le_div_of_nonneg_right hq (by linarith)
    _ ≤ (ell^2/(5/2))/(1-correction L*(ell^2/(5/2))) :=
      div_le_div_of_nonneg_left (by positivity) hd (by linarith)
    _ ≤ denominator c L := hcertificate
    _ ≤ denominator c z := denominator_mono c hc hLp hLz



end
end ReciprocalFiniteWindow

theorem solution
    (L U ell z : ℝ) (hL : 40 ≤ L) (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4 * U) ≤ ell)
    (hpositive : ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (5 / 2)) < 1)
    (hcertificate : ell ^ 2 / (5 / 2) /
        (1 - ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (5 / 2))) ≤
      ∑ q ∈ Finset.Icc 1 ⌊L⌋₊,
        (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / L)) :
    (Real.log (4 * z)) ^ 2 / (2 * TaoFivePrimes.twinPrimeConstant) /
        (1 - ((z + 1) * ((Real.log (4 * z)) ^ 2 /
          (2 * TaoFivePrimes.twinPrimeConstant)) / (16 * z ^ 2))) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then
            ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) / (1 + (q : ℝ) / z) := by
  classical
  let c : ℕ → ℝ := fun q => if Squarefree q then
    ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0
  have hc : ∀ q, 0 ≤ c q := by
    intro q
    dsimp [c]
    split_ifs
    · apply Finset.prod_nonneg
      intro p hp
      split_ifs with hp2
      · norm_num
      · have hp3 : 3 ≤ p := by
          have := (Nat.prime_of_mem_primeFactors hp).two_le
          omega
        have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
        apply div_nonneg (by norm_num)
        linarith
    · exact le_rfl
  have hC : (5/4 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant := by
    have h := PrimePairSieve.sieve_constants_certificate.1
    norm_num at h ⊢
    exact h
  have h := ReciprocalFiniteWindow.interval_certificate c hc
    TaoFivePrimes.twinPrimeConstant L U ell z hC hL hLz hzU hlog hpositive hcertificate
  simpa [ReciprocalFiniteWindow.correction, ReciprocalFiniteWindow.denominator, c,
    div_mul_eq_mul_div, mul_div_assoc] using h

#print axioms solution

-- Worked finite certificate, included for reproducibility of the first real window.
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 10000

namespace ReciprocalFirstWindow

lemma log_upper : Real.log (4*(42:ℝ)) ≤ 513/100 := by
  have h := Real.log_div_le_sum_range_add (x := (5/37:ℝ)) (by norm_num) (by norm_num) 2
  norm_num [Finset.sum_range_succ] at h
  have heq : Real.log (168:ℝ) = 7*Real.log 2 + Real.log (21/16:ℝ) := by
    rw [show (168:ℝ) = 2^7*(21/16) by norm_num, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  norm_num
  rw [heq]
  linarith [Real.log_two_lt_d9]

lemma endpoint_lower :
    (11:ℝ) ≤ ∑ q ∈ Finset.Icc (1 : ℕ) 40,
      (if Squarefree q then
      ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) / (1 + (q : ℝ) / 40) := by
  classical
  have hs1 : Squarefree 1 := by decide +kernel
  have hf1 : Nat.primeFactors 1 = (∅ : Finset ℕ) := by decide +kernel
  have hs2 : Squarefree 2 := by decide +kernel
  have hf2 : Nat.primeFactors 2 = ({2} : Finset ℕ) := by decide +kernel
  have hs3 : Squarefree 3 := by decide +kernel
  have hf3 : Nat.primeFactors 3 = ({3} : Finset ℕ) := by decide +kernel
  have hs4 : ¬Squarefree 4 := by decide +kernel
  have hs5 : Squarefree 5 := by decide +kernel
  have hf5 : Nat.primeFactors 5 = ({5} : Finset ℕ) := by decide +kernel
  have hs6 : Squarefree 6 := by decide +kernel
  have hf6 : Nat.primeFactors 6 = ({2,3} : Finset ℕ) := by decide +kernel
  have hs7 : Squarefree 7 := by decide +kernel
  have hf7 : Nat.primeFactors 7 = ({7} : Finset ℕ) := by decide +kernel
  have hs8 : ¬Squarefree 8 := by decide +kernel
  have hs9 : ¬Squarefree 9 := by decide +kernel
  have hs10 : Squarefree 10 := by decide +kernel
  have hf10 : Nat.primeFactors 10 = ({2,5} : Finset ℕ) := by decide +kernel
  have hs11 : Squarefree 11 := by decide +kernel
  have hf11 : Nat.primeFactors 11 = ({11} : Finset ℕ) := by decide +kernel
  have hs12 : ¬Squarefree 12 := by decide +kernel
  have hs13 : Squarefree 13 := by decide +kernel
  have hf13 : Nat.primeFactors 13 = ({13} : Finset ℕ) := by decide +kernel
  have hs14 : Squarefree 14 := by decide +kernel
  have hf14 : Nat.primeFactors 14 = ({2,7} : Finset ℕ) := by decide +kernel
  have hs15 : Squarefree 15 := by decide +kernel
  have hf15 : Nat.primeFactors 15 = ({3,5} : Finset ℕ) := by decide +kernel
  have hs16 : ¬Squarefree 16 := by decide +kernel
  have hs17 : Squarefree 17 := by decide +kernel
  have hf17 : Nat.primeFactors 17 = ({17} : Finset ℕ) := by decide +kernel
  have hs18 : ¬Squarefree 18 := by decide +kernel
  have hs19 : Squarefree 19 := by decide +kernel
  have hf19 : Nat.primeFactors 19 = ({19} : Finset ℕ) := by decide +kernel
  have hs20 : ¬Squarefree 20 := by decide +kernel
  have hs21 : Squarefree 21 := by decide +kernel
  have hf21 : Nat.primeFactors 21 = ({3,7} : Finset ℕ) := by decide +kernel
  have hs22 : Squarefree 22 := by decide +kernel
  have hf22 : Nat.primeFactors 22 = ({2,11} : Finset ℕ) := by decide +kernel
  have hs23 : Squarefree 23 := by decide +kernel
  have hf23 : Nat.primeFactors 23 = ({23} : Finset ℕ) := by decide +kernel
  have hs24 : ¬Squarefree 24 := by decide +kernel
  have hs25 : ¬Squarefree 25 := by decide +kernel
  have hs26 : Squarefree 26 := by decide +kernel
  have hf26 : Nat.primeFactors 26 = ({2,13} : Finset ℕ) := by decide +kernel
  have hs27 : ¬Squarefree 27 := by decide +kernel
  have hs28 : ¬Squarefree 28 := by decide +kernel
  have hs29 : Squarefree 29 := by decide +kernel
  have hf29 : Nat.primeFactors 29 = ({29} : Finset ℕ) := by decide +kernel
  have hs30 : Squarefree 30 := by decide +kernel
  have hf30 : Nat.primeFactors 30 = ({2,3,5} : Finset ℕ) := by decide +kernel
  have hs31 : Squarefree 31 := by decide +kernel
  have hf31 : Nat.primeFactors 31 = ({31} : Finset ℕ) := by decide +kernel
  have hs32 : ¬Squarefree 32 := by decide +kernel
  have hs33 : Squarefree 33 := by decide +kernel
  have hf33 : Nat.primeFactors 33 = ({3,11} : Finset ℕ) := by decide +kernel
  have hs34 : Squarefree 34 := by decide +kernel
  have hf34 : Nat.primeFactors 34 = ({2,17} : Finset ℕ) := by decide +kernel
  have hs35 : Squarefree 35 := by decide +kernel
  have hf35 : Nat.primeFactors 35 = ({5,7} : Finset ℕ) := by decide +kernel
  have hs36 : ¬Squarefree 36 := by decide +kernel
  have hs37 : Squarefree 37 := by decide +kernel
  have hf37 : Nat.primeFactors 37 = ({37} : Finset ℕ) := by decide +kernel
  have hs38 : Squarefree 38 := by decide +kernel
  have hf38 : Nat.primeFactors 38 = ({2,19} : Finset ℕ) := by decide +kernel
  have hs39 : Squarefree 39 := by decide +kernel
  have hf39 : Nat.primeFactors 39 = ({3,13} : Finset ℕ) := by decide +kernel
  have hs40 : ¬Squarefree 40 := by decide +kernel
  have hI : Finset.Icc (1 : ℕ) 40 = {1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40} := by decide +kernel
  norm_num [hI, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs28, hs29, hs30, hs31, hs32, hs33, hs34, hs35, hs36, hs37, hs38, hs39, hs40, hf1, hf2, hf3, hf5, hf6, hf7, hf10, hf11, hf13, hf14, hf15, hf17, hf19, hf21, hf22, hf23, hf26, hf29, hf30, hf31, hf33, hf34, hf35, hf37, hf38, hf39]

theorem first_interval (z : ℝ) (hz : 40 ≤ z) (hz42 : z ≤ 42) :
    Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant) /
      (1-((z+1)*(Real.log (4*z)^2/(2*TaoFivePrimes.twinPrimeConstant))/(16*z^2))) ≤
      ∑ q ∈ Finset.Icc 1 ⌊z⌋₊,
        (if Squarefree q then
      ∏ p ∈ q.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2) else 0) / (1 + (q : ℝ)/z) := by
  apply solution 40 42 (513/100) z (by norm_num) hz hz42 log_upper (by norm_num)
  have h : (513/100:ℝ)^2/(5/2)/(1-((40+1)/(16*40^2))*((513/100)^2/(5/2))) ≤ 11 := by norm_num
  simpa using h.trans endpoint_lower

#print axioms first_interval
end ReciprocalFirstWindow
