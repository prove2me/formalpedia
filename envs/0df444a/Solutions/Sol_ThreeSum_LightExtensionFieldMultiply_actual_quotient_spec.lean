-- Prove2me | solution 1 for ThreeSum.LightExtensionFieldMultiply.actual_quotient_spec
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:20.427485+00:00
-- url     : https://prove2.me/submissions/ac5e8f1c-6e97-4ffd-ac86-b1ce99da7bbd

import Definitions.Def_Submission_ThreeSum_LightExtensionMultiplyTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightExtensionFieldMultiply
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
import Theorems.Thm_ThreeSum_LightPairSearch_first_le
import Theorems.Thm_ThreeSum_LightPolynomialCoefficient_raw_zero
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_first_quotient_code
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
open ThreeSum ThreeSum.LightExtensionFieldMultiply
open Light TernaryExtensionEncoding
set_option maxHeartbeats 2000000
attribute [local instance] ThreeSum.LightExtensionFieldMultiply._p2m_local_instance_74f6067cfd_8
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}
namespace ThreeSum.LightExtensionFieldMultiply
theorem _root_.solution (C : LightExtensionQuotientPredicate.Layout)
    (hCp : C.p=p) (hCd : C.dim=f.natDegree) (hf : f.Monic) (hd : 0 < f.natDegree)
    {c : ℕ} (hc : c < p^f.natDegree) (hm : monicOfCode (p := p) f.natDegree c=f) :
    ∀ a < p^f.natDegree, ∀ b < p^f.natDegree,
      let q := p^f.natDegree
      let z := LightPairSearch.first (LightPairSearch.goodCode q
        (LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
          (LightExtensionQuotientPredicate.digits C.p b)
          (codeDigits (p := p) (c+p^f.natDegree)))) (q*q)
      0 < z ∧ z ≤ q*q ∧ (z-1)%q=encodedMul hf a b := by
  intro a ha b hb
  have hs := first_quotient_code hf hd hc ha hb hm
  dsimp only
  have he : LightExtensionQuotientSearch.good C (LightExtensionQuotientPredicate.digits C.p a)
      (LightExtensionQuotientPredicate.digits C.p b) (codeDigits (p := p) (c+p^f.natDegree))=
      quotientGood (p := p) f.natDegree c a b := by
    funext u v
    unfold LightExtensionQuotientSearch.good quotientGood
    simp only [hCp,hCd,
      LightExtensionQuotientPredicate.digits,LightCoefficientDecode.digit,codeDigits]
    rfl
  rw [he]
  exact ⟨hs.1,LightPairSearch.first_le _ _,hs.2⟩
end ThreeSum.LightExtensionFieldMultiply
