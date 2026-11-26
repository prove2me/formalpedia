-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_mk__eq_iff_55bc676ba895
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:48.996839+00:00
-- url     : https://prove2.me/submissions/95453c2b-276b-463c-9913-e369f9e92162

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_map_mul_mk__468d7c4e3210
import Theorems.Thm_NagataFactoriality_IsLocalization_algebraMap_injective
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
theorem _root_.solution {a b s t : α} (hs : s ∈ S) (ht : t ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ = _root_.IsLocalization.mk' β b ⟨t, ht⟩ ↔ a * t = b * s := by
  constructor
  · intro h
    have h' := (_root_.IsLocalization.mk'_eq_iff_eq' (M := S) (S := β)).1 h
    exact algebraMap_injective (α := α) (β := β) S <| by
      simpa [map_mul, mul_assoc, mul_left_comm, mul_comm] using h'
  · intro h
    exact _root_.IsLocalization.mk'_eq_of_eq' (M := S) (S := β) <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h.symm
end NagataFactoriality.IsLocalization
