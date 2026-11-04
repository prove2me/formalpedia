-- Prove2me | solution 1 for ThreeSum.LightPolynomialCoefficient.raw_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:08:55.433729+00:00
-- url     : https://prove2.me/submissions/fcd3ee44-ed49-468a-858e-14a532b1f8a7

import Definitions.Def_Submission_ThreeSum_LightRadixDigit
import Definitions.Def_Submission_ThreeSum_LightPolynomialCoefficient
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero

set_option autoImplicit false
open ThreeSum ThreeSum.LightPolynomialCoefficient
open Light Finset
set_option maxHeartbeats 2000000
namespace ThreeSum.LightPolynomialCoefficient
theorem _root_.solution (f g : ℕ → ℕ) {n m k j p : ℕ}
    (hf : ∀ i<n, f i<p) (hg : ∀ i<m, g i<p) (hj : j≤n) :
    rawCoefficient f g j m k≤j*p^2 := by
  unfold rawCoefficient
  calc
    ∑ i ∈ range j, term f g m k i≤∑ _i ∈ range j, p^2 := by
      apply sum_le_sum
      intro i hi
      unfold term
      split_ifs with h
      · have hfi := hf i ((mem_range.mp hi).trans_le hj)
        have hgi := hg (k-i) h.2
        nlinarith
      · omega
    _ = _ := by simp
end ThreeSum.LightPolynomialCoefficient
