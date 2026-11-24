-- Prove2me | solution 1 for PrimePairSieve.reciprocal_interval_certificate_with_constant
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T20:09:03.510757+00:00
-- url     : https://prove2.me/submissions/6cd7a8af-1b85-4208-87b3-c5c4e96be2de

import Mathlib
import Definitions.Def_TaoFivePrimes_SingularSeries

open scoped BigOperators
set_option autoImplicit false

namespace ReciprocalFiniteWindowParam
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
    (C c₀ L U ell z : ℝ) (hc₀ : 0 < c₀) (hC : c₀ ≤ C) (hL : 40 ≤ L)
    (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4*U) ≤ ell)
    (hpositive : correction L * (ell^2/(2*c₀)) < 1)
    (hcertificate : ell^2/(2*c₀)/(1-correction L*(ell^2/(2*c₀))) ≤ denominator c L) :
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
  have hq : Real.log (4*z)^2/(2*C) ≤ ell^2/(2*c₀) := by
    calc
      _ ≤ ell^2/(2*C) := div_le_div_of_nonneg_right
        (pow_le_pow_left₀ hl0 (hlU.trans hlog) 2) (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg ell) (by positivity) (by linarith)
  have hg : correction z ≤ correction L := correction_antitone hLp hLz
  have hg0 : 0 ≤ correction z := by unfold correction; positivity
  have hq0 : 0 ≤ Real.log (4*z)^2/(2*C) := by positivity
  have hgq : correction z*(Real.log (4*z)^2/(2*C)) ≤
      correction L*(ell^2/(2*c₀)) := mul_le_mul hg hq hq0 (by unfold correction; positivity)
  have hd : 0 < 1-correction L*(ell^2/(2*c₀)) := by linarith
  calc
    _ ≤ (ell^2/(2*c₀))/(1-correction z*(Real.log (4*z)^2/(2*C))) :=
      div_le_div_of_nonneg_right hq (by linarith)
    _ ≤ (ell^2/(2*c₀))/(1-correction L*(ell^2/(2*c₀))) :=
      div_le_div_of_nonneg_left (by positivity) hd (by linarith)
    _ ≤ denominator c L := hcertificate
    _ ≤ denominator c z := denominator_mono c hc hLp hLz



end
end ReciprocalFiniteWindowParam

theorem solution
    (c₀ L U ell z : ℝ) (hc₀ : 0 < c₀) (hC : c₀ ≤ TaoFivePrimes.twinPrimeConstant) (hL : 40 ≤ L) (hLz : L ≤ z) (hzU : z ≤ U)
    (hlog : Real.log (4 * U) ≤ ell)
    (hpositive : ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (2*c₀)) < 1)
    (hcertificate : ell ^ 2 / (2*c₀) /
        (1 - ((L + 1) / (16 * L ^ 2)) * (ell ^ 2 / (2*c₀))) ≤
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
  have h := ReciprocalFiniteWindowParam.interval_certificate c hc
    TaoFivePrimes.twinPrimeConstant c₀ L U ell z hc₀ hC hL hLz hzU hlog hpositive hcertificate
  simpa [ReciprocalFiniteWindowParam.correction, ReciprocalFiniteWindowParam.denominator, c,
    div_mul_eq_mul_div, mul_div_assoc] using h

#print axioms solution
