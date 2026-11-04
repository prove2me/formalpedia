-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.joined_product_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:19:47.668123+00:00
-- url     : https://prove2.me/submissions/e7c8b3ab-00ce-496d-891f-22261ae5948c

import Definitions.Def_Submission_ThreeSum_KaratsubaBounds
import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Logs
import Definitions.Def_Submission_ThreeSum_LightKaratsuba
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Theorems.Thm_ThreeSum_LightKaratsuba_ProductAt_window
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_drop
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_plus
import Theorems.Thm_ThreeSum_Karatsuba_CoeffBound_take
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_split
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


attribute [local simp] ThreeSum.LightKaratsuba.window_sub

set_option autoImplicit false
open ThreeSum ThreeSum.LightKaratsuba
open Light
open ThreeSum.Karatsuba
open Polynomial
namespace ThreeSum.LightKaratsuba
theorem _root_.solution {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : ProductAt μ work half (as.take half) (bs.take half))
    (h2 : ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : ProductAt μ (work + 2 * n) half
      (plus (as.take half) (as.drop half)) (plus (bs.take half) (bs.drop half)))
    (j : ℕ) : joined μ work n half j = (asPolynomial as * asPolynomial bs).coeff j := by
  have ha0 : (as.take half).length ≤ half := by simp
  have hb0 : (bs.take half).length ≤ half := by simp
  have ha1 : (as.drop half).length ≤ half := by simp only [List.length_drop, ha]; omega
  have hb1 : (bs.drop half).length ≤ half := by simp only [List.length_drop, hb]; omega
  have has : (plus (as.take half) (as.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le ha0 ha1
  have hbs : (plus (bs.take half) (bs.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le hb0 hb1
  have hw0 := h0.window ha0 hb0 0 j
  have hw0m := h0.window ha0 hb0 half j
  have hw2m := h2.window ha1 hb1 half j
  have hw2 := h2.window ha1 hb1 n j
  have hwm := hm.window has hbs half j
  rw [hhalf] at hw0 hw0m hw2m hw2 hwm
  unfold joined
  rw [window_sub, window_sub, hw0, hwm, hw0m, hw2m, hw2]
  simp only [pow_zero, one_mul]
  have hp :
      asPolynomial (as.take half) * asPolynomial (bs.take half) +
        (X ^ half * (asPolynomial (plus (as.take half) (as.drop half)) *
          asPolynomial (plus (bs.take half) (bs.drop half))) -
         X ^ half * (asPolynomial (as.take half) * asPolynomial (bs.take half)) -
         X ^ half * (asPolynomial (as.drop half) * asPolynomial (bs.drop half))) +
        X ^ n * (asPolynomial (as.drop half) * asPolynomial (bs.drop half)) =
      asPolynomial as * asPolynomial bs := by
    rw [asPolynomial_plus, asPolynomial_plus]
    conv_rhs => rw [asPolynomial_split half as, asPolynomial_split half bs]
    rw [← hhalf, two_mul, pow_add]
    ring
  simpa only [Polynomial.coeff_add, Polynomial.coeff_sub] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) hp
end ThreeSum.LightKaratsuba
