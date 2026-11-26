-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_mk__one_c35a0e31849c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:43.83641+00:00
-- url     : https://prove2.me/submissions/66dae17a-207a-4c7f-bdb6-7857247f818b

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization
import Theorems.Thm_P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
import Theorems.Thm_NagataFactoriality_listProd_cons
import Theorems.Thm_NagataFactoriality_listProd_nil
attribute [local simp] NagataFactoriality.listProd_cons
attribute [local simp] NagataFactoriality.listProd_nil


attribute [local simp] NagataFactoriality.IsLocalization.mk'_mul_map

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (a : α) :
    _root_.IsLocalization.mk' β a ⟨1, S.one_mem⟩ = algebraMap α β a := by
  simpa only [map_one, mul_one] using mk'_mul_map (S := S) (β := β) a 1 S.one_mem
end NagataFactoriality.IsLocalization
