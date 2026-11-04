-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_expected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:48.106028+00:00
-- url     : https://prove2.me/submissions/eee456dc-e9df-408e-8010-be8ed46c5e66

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
theorem _root_.solution (d : ℕ) (h f r : ℕ → ℕ)
    (hr : ∀ k, d≤k → r k=0) :
    arrayPolynomial (p := p) (2*d) (LightPolynomialQuotientCheck.expected p d h f r)=
      arrayPolynomial d h*arrayPolynomial (d+1) f+arrayPolynomial d r := by
  ext k
  by_cases hk : k<2*d
  · rw [arrayPolynomial_coeff,if_pos hk,coeff_add,arrayPolynomial_product_coeff,
      arrayPolynomial_coeff]
    simp only [LightPolynomialQuotientCheck.expected,ZMod.natCast_mod,Nat.cast_add]
    by_cases hkd : k<d
    · simp [hkd]
    · simp [hkd,hr k (by omega)]
  · rw [arrayPolynomial_coeff,if_neg hk,coeff_add,
      arrayPolynomial_product_zero d (d+1) k h f (by omega),arrayPolynomial_coeff,
      if_neg (by omega : ¬k<d)]
    simp
end ThreeSum.TernaryExtensionEncoding
