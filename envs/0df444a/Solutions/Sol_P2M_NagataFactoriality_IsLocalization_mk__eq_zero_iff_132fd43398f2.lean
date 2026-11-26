-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_mk__eq_zero_iff_132fd43398f2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:57.01155+00:00
-- url     : https://prove2.me/submissions/f46f0910-6f29-41e3-b2cd-ba125f940a04

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.IsLocalization.mk'_mul_map
attribute [local simp] NagataFactoriality.IsLocalization.mk'_one
attribute [local simp] NagataFactoriality.IsLocalization.map_mul_mk'

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
variable [IsDomain α] [Fact ((0 : α) ∉ S)]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution {a s : α} (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = 0 ↔ a = 0 := by
  have h := mk'_eq_iff (S := S) (β := β) (a := a) (b := 0) (s := s) (t := 1) hs S.one_mem
  simpa using h
end NagataFactoriality.IsLocalization
