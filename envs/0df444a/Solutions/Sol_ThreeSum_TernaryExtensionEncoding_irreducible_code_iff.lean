-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.irreducible_code_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:19:58.998035+00:00
-- url     : https://prove2.me/submissions/613d5ef4-d030-40a8-a32d-5baf1ca196a8

import Definitions.Def_Submission_ThreeSum_TernaryProductCheckerExact
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
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
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_irreducible_iff_no_monic_factors
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_degree
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_monicCandidate_monic
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
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d c : ℕ} (hd : 0<d) :
    Irreducible (monicOfCode (p := p) d c) ↔
    ∀ e, 0<e → e<d → ∀ u<p^e, ∀ v<p^(d-e),
      monicOfCode (p := p) e u*monicOfCode (d-e) v≠monicOfCode d c := by
  rw [irreducible_iff_no_monic_factors (show (monicOfCode (p := p) d c).Monic from monicCandidate_monic _)
    (show (monicOfCode (p := p) d c).natDegree=d from monicCandidate_degree _) hd]
  constructor
  · intro h e he hed u hu v hv
    exact h e he hed _ _
  · intro h e he hed a b
    have hh := h e he hed (coefficientCode a) (coefficientCode_lt a)
      (coefficientCode b) (coefficientCode_lt b)
    simpa only [monicOfCode,coefficientVector_code] using hh
end ThreeSum.TernaryExtensionEncoding
