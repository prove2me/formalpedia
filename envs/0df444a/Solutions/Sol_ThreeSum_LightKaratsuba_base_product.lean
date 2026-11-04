-- Prove2me | solution 1 for ThreeSum.LightKaratsuba.base_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:16:03.416319+00:00
-- url     : https://prove2.me/submissions/1ab72489-043b-488d-89f8-e56da9047eed

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
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_head
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
variable {lim : Limits} {P : Program} {d : ℕ}
namespace ThreeSum.LightKaratsuba
theorem _root_.solution {μ μ' : ℕ → ℤ} {a b out : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs)
    (hAlen : as.length = 1) (hBlen : bs.length = 1)
    (hzero : μ' out = μ a * μ b) (hone : μ' (out + 1) = 0) :
    ProductAt μ' out 1 as bs := by
  have hA := asPolynomial_head hAlen.le
  have hB := asPolynomial_head hBlen.le
  have hhead (xs : List ℤ) : xs.getD 0 0 = xs.headD 0 := by cases xs <;> rfl
  have hreadA : μ a = as.headD 0 := by
    simpa only [Nat.add_zero, hhead] using ha.getD (by omega : 0 < as.length) 0
  have hreadB : μ b = bs.headD 0 := by
    simpa only [Nat.add_zero, hhead] using hb.getD (by omega : 0 < bs.length) 0
  intro j hj
  rw [hA, hB, ← map_mul]
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simpa only [Nat.add_zero, Polynomial.coeff_C_zero, hreadA, hreadB] using hzero
  · simpa only [Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0)] using hone
end ThreeSum.LightKaratsuba
