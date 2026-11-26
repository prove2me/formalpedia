-- Prove2me | solution 1 for P2M_NagataFactoriality_IsLocalization_mk__mul_map_9c61a4ca4225
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:48:13.320889+00:00
-- url     : https://prove2.me/submissions/1374eaca-7522-48bb-bc13-f76eb36b88bc

import Mathlib.RingTheory.Localization.Basic
import Definitions.Def_NagataFactoriality_Localization_MultSet
import Definitions.Def_NagataFactoriality_Localization_IsLocalization

set_option autoImplicit false
open NagataFactoriality
open NagataFactoriality.IsLocalization
variable {α β : Type*} [CommRing α] [CommRing β] {S : Submonoid α}
variable [Algebra α β] [_root_.IsLocalization S β]
namespace NagataFactoriality.IsLocalization
theorem _root_.solution (a s : α) (hs : s ∈ S) :
    _root_.IsLocalization.mk' β a ⟨s, hs⟩ * algebraMap α β s = algebraMap α β a := by
  exact _root_.IsLocalization.mk'_spec_mk (M := S) (S := β) a s hs
end NagataFactoriality.IsLocalization
