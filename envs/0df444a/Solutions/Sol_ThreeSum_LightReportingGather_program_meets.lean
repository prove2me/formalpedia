-- Prove2me | solution 1 for ThreeSum.LightReportingGather.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:35.580686+00:00
-- url     : https://prove2.me/submissions/3ff0edce-aafd-41b0-80bd-dfee8db927fa

import Definitions.Def_Submission_ThreeSum_LightReportingFilter
import Definitions.Def_Submission_ThreeSum_LightReportingGather
import Theorems.Thm_ThreeSum_LightReportingGather_meets
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_Meets_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_LightReportingAffine_meets
import Definitions.Def_WeightedCache3SUM_Alias_62113581f113eb47
import Theorems.Thm_ThreeSum_LightReportingFilter_mem_selected
import Theorems.Thm_ThreeSum_LightReportingFilter_selected_zero
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.LightReportingFilter.mem_selected
attribute [local simp] ThreeSum.LightReportingFilter.selected_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightReportingGather
open Light
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightReportingGather
theorem _root_.solution {μ : ℕ → ℤ} {indices src dst t n d : ℕ}
    (index : ℕ → ℕ) (value : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrc : src+n ≤ lim.space) (hdst : dst+t ≤ lim.space)
    (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src+i) = value i)
    (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim program 0 d [indices,src,dst,t,n] μ (time t)
      (fun _ ν => Seg ν dst (List.ofFn fun i : Fin t => value (index i.val)) ∧
        SameOutside μ ν dst t) := by
  apply (meets rfl index value hw hindices hsrc hdst hsepI hsepS hindex hreadI hreadS hword).mono le_rfl
  rintro r ν ⟨hout,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro i hi
  have hi' : i < t := by simpa only [List.length_ofFn] using hi
  simpa only [List.getElem_ofFn] using hout i hi'
end ThreeSum.LightReportingGather
