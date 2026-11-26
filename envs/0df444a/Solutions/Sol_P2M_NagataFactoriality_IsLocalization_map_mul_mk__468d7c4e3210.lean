-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:49:23.002801+00:00
-- url     : https://prove2.me/submissions/a9f0f53d-6fc2-4b0b-8d03-973a16ca170a

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.IsLocalization.mk'_mul_map
attribute [local simp] NagataFactoriality.IsLocalization.mk'_one

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (a b s : α) (hs : s ∈ S) :
    algebraMap α β a * _root_.IsLocalization.mk' β b ⟨s, hs⟩ =
      _root_.IsLocalization.mk' β (a * b) ⟨s, hs⟩ := by
  simpa using (_root_.IsLocalization.mul_mk'_eq_mk'_of_mul (M := S) (S := β) a b ⟨s, hs⟩)
end NagataFactoriality.IsLocalization
