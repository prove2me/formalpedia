-- Prove2me | solution 1 for ThreeSum.WeightedGlobalOversizeOverhead.baseFactor_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:42:01.983171+00:00
-- url     : https://prove2.me/submissions/40796e5e-2dd5-4322-b28f-ebf1913700dd

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeRates
import Definitions.Def_Submission_Weighted_Global_TernaryRadixOverhead
import Definitions.Def_Submission_Weighted_Global_TernaryOversizeOverhead
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_native_cap_exponent_bound
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_baseFrequency_upper
import Theorems.Thm_ThreeSum_WeightedGlobalOversizeOverhead_baseFactor_pos
import Theorems.Thm_ThreeSum_Parameters_log_two_pos
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalEntropyRates_denominator_pos
import Theorems.Thm_ThreeSum_WeightedGlobalParameters_log_two_pos


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalOversizeOverhead
open Filter Real WeightedGlobalParameters WeightedGlobalEntropyRates WeightedGlobalCoverScale
open WeightedGlobalLocalParameters TernaryCoverLocal WeightedGlobalOversizePrime WeightedGlobalOversizeRates
open WeightedGlobalCoverFrequency WeightedGlobalCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000
namespace ThreeSum.WeightedGlobalOversizeOverhead
theorem _root_.solution {K k m : ℕ} (hK : 0 < K) (hk : 0 < k) (hm : 0 < m) (c d : ℕ) :
    Real.log (baseFactor K k c d m : ℝ)/((fixedLength m : ℝ)*Real.log 2) ≤ rateUpper k c d m := by
  have hL : fixedLength m+1 ≤ 2^45*(m+1) := by unfold fixedLength; norm_num; omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left (max 1 c) (Nat.pow_le_pow_left hL d)) (baseFrequency_upper hK m)
  have hpoly : (max 1 c)*(fixedLength m+1)^d*baseFrequency K m ≤
      (max 1 c)*2^(361+45*d)*(m+1)^(d+7) := by
    convert hp using 1 <;> rw [mul_pow,← pow_mul,pow_add] <;> ring
  have hbound := Nat.mul_le_mul_right (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) hpoly
  have hpos : 0 < (baseFactor K k c d m : ℝ) := by exact_mod_cast baseFactor_pos K k c d m
  have hboundN : baseFactor K k c d m ≤ (max 1 c)*2^(361+45*d)*(m+1)^(d+7)*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k := hbound
  have hboundR : (baseFactor K k c d m : ℝ) ≤
      (((max 1 c)*2^(361+45*d)*(m+1)^(d+7)*
        rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ) := by exact_mod_cast hboundN
  have hlog := Real.log_le_log hpos hboundR
  have hc : (0 : ℝ) < max 1 c := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left 1 c)
  have hmp : (0 : ℝ) < (m+1 : ℕ) := by positivity
  have htpos : (0 : ℝ) < rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k := by
    exact_mod_cast rawThreshold_pos (nativePrime K m) (sourceCap m (nativePrime K m)) k
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow] at hlog
  have hτ : Real.log (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ)=
      (capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ)*Real.log 2 := by
    unfold rawThreshold
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
  rw [hτ] at hlog
  have he : (k : ℝ)*(capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ) ≤
      20*(fixedLength m : ℝ)+8*(k : ℝ)^2+26+k := by exact_mod_cast native_cap_exponent_bound hK m k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd := denominator_pos hm
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  apply (div_le_iff₀ hd).mpr
  unfold rateUpper
  field_simp [hkR.ne',hLen,log_two_pos.ne']
  push_cast
  push_cast at hlog
  have hlogk := mul_le_mul_of_nonneg_right hlog hkR.le
  have hh := mul_le_mul_of_nonneg_right he log_two_pos.le
  nlinarith
end ThreeSum.WeightedGlobalOversizeOverhead
