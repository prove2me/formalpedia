-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_extend
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:14:46.620416+00:00
-- url     : https://prove2.me/submissions/58853f68-3764-4969-95e9-8db3f04bef62

import Definitions.Def_Submission_ThreeSum_TernaryMonicCodes
import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
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
theorem _root_.solution (n len : ℕ) (a : ℕ → ℕ) (hn : n≤len)
    (hz : ∀ k, n≤k → a k=0) :
    arrayPolynomial (p := p) len a=arrayPolynomial n a := by
  ext k
  simp only [arrayPolynomial_coeff]
  by_cases hk : k<n
  · simp [hk,show k<len by omega]
  · by_cases hkl : k<len
    · simp [hk,hkl,hz k (by omega)]
    · simp [hk,hkl]
end ThreeSum.TernaryExtensionEncoding
