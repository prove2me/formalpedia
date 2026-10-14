-- Prove2me | solution 1 for TaoFivePrimes.rh_pi_enclosure_700
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-14T04:52:51.497985+00:00
-- url     : https://prove2.me/submissions/7634a57b-3575-43e8-8767-11f79806afca

import Mathlib
import Definitions.Def_TaoFivePrimes_RHPi700Numerator
set_option exponentiation.threshold 20000
namespace RH1000PiProof
section Height100Module37

set_option autoImplicit false
set_option maxHeartbeats 0
open Finset
open scoped BigOperators

namespace CertifiedHighPrecisionPi

noncomputable def atanSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma atan_remainder (x : ℝ) (hx0 : 0≤ x) (hx1 : x<1) (N : ℕ) :
    |Real.arctan x - atanSum x N| ≤  x^(2*N+1)/(1-x^2) := by
  have hx : ‖x‖<1 := by simpa [Real.norm_eq_abs,abs_of_nonneg hx0]
  have hs := Real.hasSum_arctan hx
  have htail : Real.arctan x - atanSum x N =
      ∑' n : ℕ, (-1)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1) := by
    have h := hs.summable.sum_add_tsum_nat_add N
    rw [hs.tsum_eq] at h
    exact sub_eq_iff_eq_add.mpr (by simpa [atanSum,add_comm] using h.symm)
  rw [htail, ← Real.norm_eq_abs]
  have hq0 : 0≤ x^2 := sq_nonneg x
  have hq1 : x^2<1 := by nlinarith
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (x^(2*N+1))
  have he := tsum_of_norm_bounded hgeo (fun n : ℕ => by
    have hd : (1:ℝ)≤ 2*(n+N)+1 := by
      have hn : (0:ℝ)≤ n := Nat.cast_nonneg n
      have hN : (0:ℝ)≤ N := Nat.cast_nonneg N
      linarith
    calc
      ‖(-1:ℝ)^(n+N)*x^(2*(n+N)+1)/(2*(n+N)+1)‖ =
          x^(2*(n+N)+1)/(2*(n+N)+1) := by
        simp [norm_div,norm_mul,norm_pow,Real.norm_eq_abs,abs_of_nonneg hx0,
          abs_of_nonneg (by positivity : (0:ℝ)≤ 2*(n+N)+1)]
      _ ≤  x^(2*(n+N)+1) := div_le_self (by positivity) hd
      _ = x^(2*N+1)*(x^2)^n := by
        rw [show 2*(n+N)+1=(2*N+1)+2*n by ring,pow_add,pow_mul])
  simpa only [div_eq_mul_inv] using he

noncomputable def rationalAtanSum (x : ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ range N, (-1)^n*x^(2*n+1)/(2*n+1)

lemma rationalAtanSum_cast (x : ℚ) (N : ℕ) :
    (rationalAtanSum x N : ℝ) = atanSum x N := by
  simp [rationalAtanSum,atanSum]

noncomputable def machinApprox (N M : ℕ) : ℚ :=
  16*rationalAtanSum (1/5) N - 4*rationalAtanSum (1/239) M

lemma machin_error (N M : ℕ) :
    |Real.pi-(machinApprox N M:ℝ)| ≤ 
      16*((1/5:ℝ)^(2*N+1)/(1-(1/5:ℝ)^2)) +
        4*((1/239:ℝ)^(2*M+1)/(1-(1/239:ℝ)^2)) := by
  have h5 := atan_remainder (1/5) (by norm_num) (by norm_num) N
  have h239 := atan_remainder (1/239) (by norm_num) (by norm_num) M
  have hm : Real.pi = 16*Real.arctan (1/5)-4*Real.arctan (1/239) := by
    have h := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
    norm_num at h
    linarith
  rw [hm,machinApprox]
  push_cast
  rw [rationalAtanSum_cast,rationalAtanSum_cast]
  calc
    _ = |16*(Real.arctan (1/5)-atanSum (1/5) N) -
        4*(Real.arctan (1/239)-atanSum (1/239) M)| := by congr 1; ring
    _ ≤  |16*(Real.arctan (1/5)-atanSum (1/5) N)| +
        |4*(Real.arctan (1/239)-atanSum (1/239) M)| := abs_sub _ _
    _ ≤  _ := by
      rw [abs_mul,abs_mul]
      norm_num at h5 h239 ⊢
      linarith

end CertifiedHighPrecisionPi

end Height100Module37

/- Source module: Pi310. -/
section Height100Module38

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000
set_option Elab.async false

namespace CertifiedHighPrecisionPi

lemma machin_error_720 : |Real.pi-(machinApprox 520 160:ℝ)|≤ 1/10^720 := by
  apply (machin_error 520 160).trans
  norm_num

lemma machin_lower_check : (TaoFivePrimes_RHPi700Numerator:ℚ)/10^700 + 1/10^720 ≤  machinApprox 520 160 := by
  decide +kernel

lemma machin_upper_check : machinApprox 520 160 + 1/10^720 ≤  (TaoFivePrimes_RHPi700Numerator+1:ℚ)/10^700 := by
  decide +kernel

theorem pi_enclosure_700 :
    (TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 ≤  Real.pi ∧ Real.pi ≤  (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700 := by
  have hl : (TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 + 1/10^720 ≤  (machinApprox 520 160:ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_lower_check
    push_cast at h
    exact h
  have hu : (machinApprox 520 160:ℝ) + 1/10^720 ≤  (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700 := by
    have h := (Rat.cast_le (K := ℝ)).mpr machin_upper_check
    push_cast at h
    exact h
  have he := abs_le.mp machin_error_720
  constructor <;> linarith

end CertifiedHighPrecisionPi

end Height100Module38
end RH1000PiProof

theorem solution : (TaoFivePrimes_RHPi700Numerator:ℝ)/10^700 ≤ Real.pi ∧ Real.pi ≤ (TaoFivePrimes_RHPi700Numerator+1:ℝ)/10^700 := RH1000PiProof.CertifiedHighPrecisionPi.pi_enclosure_700
