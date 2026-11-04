-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.factor_nohit_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:19.554932+00:00
-- url     : https://prove2.me/submissions/00e4c66c-960f-464e-99f9-6fe5e2f2843b

import Definitions.Def_Submission_ThreeSum_TernaryExtensionCheckerSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientSearch
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
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
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_factor_check_iff
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
open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d e c : ℕ} (hd : 0<d) (he : 0<e) (hed : e<d)
    (hc : c<p^d) :
    (∀ u<p^e, ∀ v<p^(d-e),
      ¬LightPolynomialProductCheck.Valid p (codeDigits (p := p) (u+p^e))
        (codeDigits (p := p) (v+p^(d-e))) (codeDigits (p := p) (c+p^d))
        (e+1) (d-e+1) (2*d)) ↔
    ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
      monicCandidate a*monicCandidate b≠monicOfCode d c := by
  constructor
  · intro h a b
    have hh := h (coefficientCode a) (coefficientCode_lt a)
      (coefficientCode b) (coefficientCode_lt b)
    intro hab
    apply hh
    apply (factor_check_iff hd hed hc (coefficientCode_lt a) (coefficientCode_lt b)).mpr
    simpa only [monicOfCode,coefficientVector_code] using hab
  · intro h u hu v hv hg
    exact h _ _ ((factor_check_iff hd hed hc hu hv).mp hg)
end ThreeSum.TernaryExtensionEncoding
