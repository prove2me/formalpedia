-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.product_valid_iff_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:17:41.84189+00:00
-- url     : https://prove2.me/submissions/6362094a-5c24-4248-ae2d-3510cd498bf3

import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_product_zero
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_coeff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_arrayPolynomial_product_coeff
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_product_valid_coefficients
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices
attribute [local simp] ThreeSum.LightPolynomialCoefficient.raw_zero



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (a b expected : ℕ → ℕ) (n m len : ℕ)
    (hlen : n+m-1≤len) (hb : ∀ k<len, expected k<p) :
    LightPolynomialProductCheck.Valid p a b expected n m len ↔
      arrayPolynomial n a*arrayPolynomial m b=arrayPolynomial (p := p) len expected := by
  constructor
  · intro h
    ext k
    by_cases hk : k<len
    · rw [arrayPolynomial_coeff,if_pos hk]
      exact product_valid_coefficients a b expected n m len h k hk
    · rw [arrayPolynomial_product_zero n m k a b (by omega),arrayPolynomial_coeff,if_neg hk]
  · intro h k hk
    have hc := congrArg (fun f : (ZMod p)[X] => f.coeff k) h
    rw [arrayPolynomial_product_coeff,arrayPolynomial_coeff,if_pos hk] at hc
    have hv := congrArg ZMod.val hc
    simpa [LightPolynomialCoefficient.coefficient,ZMod.val_natCast,
      Nat.mod_eq_of_lt (hb k hk)] using hv.symm
end ThreeSum.TernaryExtensionEncoding
