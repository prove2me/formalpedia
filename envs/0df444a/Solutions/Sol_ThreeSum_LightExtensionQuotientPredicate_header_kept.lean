-- Prove2me | solution 1 for ThreeSum.LightExtensionQuotientPredicate.header_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:19:08.435215+00:00
-- url     : https://prove2.me/submissions/a461f8cb-bd48-4673-94c0-1304d0db83fa

import Definitions.Def_Submission_ThreeSum_LightPolynomialQuotientCheck
import Definitions.Def_Submission_ThreeSum_LightExtensionQuotientPredicate
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
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
open ThreeSum ThreeSum.LightExtensionQuotientPredicate
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program} {depth : ℕ}
namespace ThreeSum.LightExtensionQuotientPredicate
theorem _root_.solution {C : Layout} {μ ν : ℕ → ℤ} {ctx keep : ℕ}
    (H : Seg μ ctx (header C)) (hctx : ctx+10≤keep) (hkeep : Kept μ ν keep) :
    Seg ν ctx (header C) := by
  intro i hi
  have hi' : i<10 := by simpa [header] using hi
  rw [hkeep _ (by omega)]
  exact H i hi
end ThreeSum.LightExtensionQuotientPredicate
