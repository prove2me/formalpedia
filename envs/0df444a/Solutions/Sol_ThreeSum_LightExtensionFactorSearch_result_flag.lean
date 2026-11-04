-- Prove2me | solution 1 for ThreeSum.LightExtensionFactorSearch.result_flag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:45.663223+00:00
-- url     : https://prove2.me/submissions/4c2bfdea-eb4d-4639-90bf-cfaa4cd1f1e4

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorPredicate
import Definitions.Def_Submission_ThreeSum_LightPairSearchProgram
import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
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
open ThreeSum ThreeSum.LightExtensionFactorSearch
open Light LightExtensionFactorPredicate
set_option maxHeartbeats 1000000
variable {lim : Limits}
attribute [local instance] ThreeSum.LightExtensionFactorSearch._p2m_local_instance_9c16afeb32_9
namespace ThreeSum.LightExtensionFactorSearch
theorem _root_.solution (C : Layout) (f : ℕ → ℕ) (u v : ℕ) :
    result C f u v=(if good C f u v then 1 else 0) := by
  by_cases hu : u<C.p^C.degree
  · by_cases hv : v<C.p^(C.dim-C.degree)
    · by_cases hval : LightPolynomialProductCheck.Valid C.p
        (LightExtensionFactorCheck.digits C.p (u+C.p^C.degree))
        (LightExtensionFactorCheck.digits C.p (v+C.p^(C.dim-C.degree))) f
        (C.degree+1) (C.dim-C.degree+1) (2*C.dim)
      · simp [result,LightPolynomialProductCheck.flag,good,hu,hv,hval]
      · simp [result,LightPolynomialProductCheck.flag,good,hu,hv,hval]
    · simp [result,good,hu,hv]
  · simp [result,good,hu]
end ThreeSum.LightExtensionFactorSearch
