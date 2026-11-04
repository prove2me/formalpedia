-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.linear_update_full
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:00.821979+00:00
-- url     : https://prove2.me/submissions/92ec83d7-cdf8-4426-8730-c6a00eb94459

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD



set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
theorem _root_.solution {μ μ' : ℕ → ℤ} {out src offset n N : ℕ}
    {c : ℤ} {f g : ℕ → ℤ} (hfit : offset + n ≤ N)
    (hOld : ∀ j < N, μ (out + j) = f j)
    (hSrc : ∀ i < n, μ (src + i) = g i)
    (hWrite : ∀ i < n,
      μ' (out + offset + i) = μ (out + offset + i) + c * μ (src + i))
    (hkeep : SameOutside μ μ' (out + offset) n) :
    ∀ j < N, μ' (out + j) = f j + window (fun i => c * g i) offset n j := by
  intro j hj
  unfold window
  split_ifs with hin
  · have hi : j - offset < n := by omega
    have he : out + offset + (j - offset) = out + j := by omega
    have hr := hWrite (j - offset) hi
    rw [he, hOld j hj, hSrc _ hi] at hr
    exact hr
  · have hr := hkeep (out + j) (by omega)
    simpa only [add_zero, hOld j hj] using hr
end ThreeSum.LightKaratsuba
