-- Prove2me | solution 1 for ThreeSum.LightZetaBatch.values_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:50.647203+00:00
-- url     : https://prove2.me/submissions/a2345133-657c-475a-9db0-84b35936c17c

import Definitions.Def_Submission_ThreeSum_LightZetaCell
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_isMask
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaBatch
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaBatch
theorem _root_.solution {L cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) :
    values μ dst (enumerateLayer L cardinal) a f S =
      if S.card = cardinal then Subset.zetaStep a f S else μ (dst+subsetRank S) := by
  have hm := subsetMask_isMask S
  simp only [values,mem_enumerateLayer,IsMask,hm.1,true_and,hm.2]
end ThreeSum.LightZetaBatch
