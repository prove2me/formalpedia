-- Prove2me | solution 1 for ThreeSumSharpTail.explicit_parameter_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-13T16:32:29.01865+00:00
-- url     : https://prove2.me/submissions/0df52585-5516-4920-b70c-c3927f210b2f

import Theorems.Thm_ThreeSumSharpTail_encoding_log_certificate
import Theorems.Thm_ThreeSumSharpTail_entropy_log_certificate
import Definitions.Def_ThreeSumSharpTail_Analysis

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 5000000
set_option exponentiation.threshold 1000
open scoped BigOperators

namespace ThreeSumSharpTail.Certificate

lemma log_seven_over_log_two_lt : Real.log 7 / Real.log 2 < (281 : ℝ) / 100 := by
  have hpow : 7 ^ 100 < (2 : ℕ) ^ 281 := by decide
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (7 : ℝ) ^ 100)
    (by exact_mod_cast hpow : (7 : ℝ) ^ 100 < (2 : ℝ) ^ 281)
  rw [Real.log_pow, Real.log_pow] at hlog
  have hden : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hscaled : Real.log 7 < (281 : ℝ) / 100 * Real.log 2 := by
    calc
      Real.log 7 < (281 * Real.log 2) / 100 := (lt_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 (by norm_num at hlog; linarith)
      _ = (281 : ℝ) / 100 * Real.log 2 := by ring
  exact (div_lt_iff₀ hden).2 hscaled

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  have hpow : (4 : ℝ) = 2 * 2 := by norm_num
  rw [hpow]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
  ring

end ThreeSumSharpTail.Certificate

theorem solution :
    (0.05665 : ℝ) * (ThreeSumSharpTail.encodingExponent 21 + ThreeSumSharpTail.sharpSaving 21 0.11202) < 1 ∧
    (0.06945 : ℝ) < ThreeSumSharpTail.sharpSaving 21 0.11202 ∧
    (0.06945 : ℝ) < 1 / 2 - ThreeSumSharpTail.queryExponent 0.11202 ∧
    Real.log 7 / Real.log 2 + 3 * (0.05665 : ℝ) / 2 < 3 - 0.05665 * 0.06945 / 2 ∧
    2 + (0.05665 : ℝ) * (1 + 0.06945 / 2) < 3 - 0.05665 * 0.06945 / 2 ∧
    (2 - (0.05665 : ℚ) * 0.06945 / 4) = 1.999016414375 ∧
    (1.999017 : ℚ) - (2 - 0.05665 * 0.06945 / 4) = 0.000000585625 := by
  rcases ThreeSumSharpTail.encoding_log_certificate with ⟨l2, l10, l3, l9, linv21, l20_21⟩
  rcases ThreeSumSharpTail.entropy_log_certificate with ⟨lu, luc, lt, ltc⟩
  have hE : (19144408 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (1 / 21) ∧
      ThreeSumSharpTail.entropy (1 / 21) ≤ 19144409 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> nlinarith [linv21.1, linv21.2, l20_21.1, l20_21.2]
  have hU : (17513847 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (44399 / 1050000) ∧
      ThreeSumSharpTail.entropy (44399 / 1050000) ≤ 17513849 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> nlinarith [lu.1, lu.2, luc.1, luc.2]
  have hT : (35071790 / 10^8 : ℝ) ≤ ThreeSumSharpTail.entropy (5601 / 50000) ∧
      ThreeSumSharpTail.entropy (5601 / 50000) ≤ 35071791 / 10^8 := by
    norm_num [ThreeSumSharpTail.entropy]
    constructor <;> linarith [lt.1, lt.2, ltc.1, ltc.2]
  have l4 : (1386294361 / 10^9 : ℝ) ≤ Real.log 4 ∧ Real.log 4 ≤ 1386294362 / 10^9 := by
    rw [ThreeSumSharpTail.Certificate.log_four_eq]
    constructor <;> linarith only [l2.1, l2.2]
  have hgamma : (69454 / 10^6 : ℝ) ≤ ThreeSumSharpTail.sharpSaving 21 (5601 / 50000) ∧
      ThreeSumSharpTail.sharpSaving 21 (5601 / 50000) ≤ 69456 / 10^6 := by
    have harg : (1 - (5601 : ℝ) / 50000) / 21 = (44399 : ℝ) / 1050000 := by norm_num
    have h4pos : 0 < Real.log 4 := by linarith only [l4.1]
    have hnlo : (69454 / 10^6 : ℝ) * Real.log 4 ≤
        21 * ThreeSumSharpTail.entropy (1 / 21) - 21 * ThreeSumSharpTail.entropy (44399 / 1050000) -
          (5601 : ℝ) / 50000 * Real.log 9 := by linarith only [hE.1, hU.2, l9.2, l4.2]
    have hnhi : 21 * ThreeSumSharpTail.entropy (1 / 21) - 21 * ThreeSumSharpTail.entropy (44399 / 1050000) -
          (5601 : ℝ) / 50000 * Real.log 9 ≤ (69456 / 10^6 : ℝ) * Real.log 4 := by
      linarith only [hE.2, hU.1, l9.1, l4.1]
    unfold ThreeSumSharpTail.sharpSaving
    rw [harg]
    constructor
    · exact (le_div_iff₀ h4pos).2 hnlo
    · exact (div_le_iff₀ h4pos).2 hnhi
  have hquery : ThreeSumSharpTail.queryExponent (5601 / 50000) ≤ (43054 / 100000 : ℝ) := by
    unfold ThreeSumSharpTail.queryExponent
    have hnum : ThreeSumSharpTail.entropy (5601 / 50000) + (5601 / 50000) * Real.log 9 ≤
        (43054 / 100000 : ℝ) * Real.log 4 := by
      linarith only [hT.2, l9.2, l4.1]
    exact (div_le_iff₀ (by linarith only [l4.1])).2 hnum
  have henc : ThreeSumSharpTail.encodingExponent 21 ≤ (17581 / 1000 : ℝ) := by
    unfold ThreeSumSharpTail.encodingExponent
    have hnum : 21 * Real.log 10 - 21 * ThreeSumSharpTail.entropy (1 / 21) / 2 - (21 - 1) * Real.log 3 ≤
        (17581 / 1000 : ℝ) * Real.log 4 := by
      norm_num
      linarith only [hE.1, l10.2, l3.1, l4.1]
    exact (div_le_iff₀ (by linarith only [l4.1])).2 hnum
  have hLogRatio := ThreeSumSharpTail.Certificate.log_seven_over_log_two_lt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num at henc hgamma ⊢
    linarith only [henc, hgamma.2]
  · norm_num at hgamma ⊢
    linarith only [hgamma.1]
  · norm_num at hquery ⊢
    linarith only [hquery]
  · norm_num at hLogRatio ⊢
    linarith only [hLogRatio]
  · norm_num
  · norm_num
  · norm_num
