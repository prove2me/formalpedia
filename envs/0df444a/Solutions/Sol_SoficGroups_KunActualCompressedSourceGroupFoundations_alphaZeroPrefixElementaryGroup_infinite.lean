-- Prove2me | solution 1 for SoficGroups.KunActualCompressedSourceGroupFoundations.alphaZeroPrefixElementaryGroup_infinite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/ca8f050b-1597-4541-87d4-3adf9662450e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_binaryLeavittEL3_infinite

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunActualCompressedSourceGroupFoundations
universe v
namespace SoficGroups.KunActualCompressedSourceGroupFoundations
theorem _root_.solution :
    Infinite
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaZeroPrefixCode) := by
  letI : Infinite (SoficGroups.binaryLeavittElementaryGroup 3) :=
    SoficGroups.binaryLeavittEL3_infinite
  exact Infinite.of_injective
    (SoficGroups.binaryPrefixElementaryGroupEquiv
      SoficGroups.alphaZeroPrefixCode)
    (SoficGroups.binaryPrefixElementaryGroupEquiv
      SoficGroups.alphaZeroPrefixCode).injective
end SoficGroups.KunActualCompressedSourceGroupFoundations
