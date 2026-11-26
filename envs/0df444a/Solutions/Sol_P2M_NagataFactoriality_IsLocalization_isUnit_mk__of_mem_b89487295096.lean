-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_isUnit_mk__of_mem_b89487295096
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:36.347524+00:00
-- url     : https://prove2.me/submissions/cc00cdd5-3fb7-4ee1-b7f0-c6dc792d0732

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_NagataFactoriality_IsLocalization_map_eq_zero_iff
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.IsLocalization.mk'_mul_map
attribute [local simp] NagataFactoriality.IsLocalization.mk'_one
attribute [local simp] NagataFactoriality.IsLocalization.map_mul_mk'
attribute [local simp] NagataFactoriality.IsLocalization.map_eq_zero_iff

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution {a s : α} (ha : a ∈ S) (hs : s ∈ S) :
    IsUnit (_root_.IsLocalization.mk' β a ⟨s, hs⟩) := by
  apply isUnit_iff_exists_inv.2
  refine ⟨_root_.IsLocalization.mk' β s ⟨a, ha⟩, ?_⟩
  simpa using (_root_.IsLocalization.mk'_mul_mk'_eq_one' (M := S) (S := β) a ⟨s, hs⟩ ha)
end NagataFactoriality.IsLocalization
