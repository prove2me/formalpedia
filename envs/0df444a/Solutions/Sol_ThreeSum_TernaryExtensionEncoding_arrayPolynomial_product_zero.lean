-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.arrayPolynomial_product_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:24:12.087394+00:00
-- url     : https://prove2.me/submissions/cbdf2856-446e-4e34-b751-426f39287980

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
theorem _root_.solution (n m k : ℕ) (a b : ℕ → ℕ)
    (hk : n+m-1≤k) :
    (arrayPolynomial (p := p) n a*arrayPolynomial m b).coeff k=0 := by
  rw [arrayPolynomial_product_coeff]
  unfold LightPolynomialCoefficient.coefficient LightPolynomialCoefficient.rawCoefficient
  have hz : (∑ i ∈ range n, LightPolynomialCoefficient.term a b m k i)=0 := by
    apply sum_eq_zero
    intro i hi
    have hin := mem_range.mp hi
    unfold LightPolynomialCoefficient.term
    split_ifs with h
    · omega
    · rfl
  rw [hz]
  simp
end ThreeSum.TernaryExtensionEncoding
