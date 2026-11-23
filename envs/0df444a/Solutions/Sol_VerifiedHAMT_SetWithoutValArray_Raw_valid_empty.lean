-- Prove2me | solution 1 for VerifiedHAMT.SetWithoutValArray.Raw.valid_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:20.842209+00:00
-- url     : https://prove2.me/submissions/7fe44801-b99b-4676-a098-61dd712b6d62

module
public import Definitions.Def_VerifiedHAMT_Basic
public import Definitions.Def_VerifiedHAMT_SetWithoutValArray_Basic
public import Theorems.Thm_VerifiedHAMT_SetWithoutValArray_Raw_wellFormed_empty
public import Theorems.Thm_VerifiedHAMT_wellFormed_empty


set_option autoImplicit true
@[expose] public section
public section
open VerifiedHAMT VerifiedHAMT.SetWithoutValArray VerifiedHAMT.SetWithoutValArray.Raw
variable {α : Type u}
open Lean.PersistentHashMap (branching)
namespace VerifiedHAMT.SetWithoutValArray.Raw
theorem _root_.solution [BEq α] [Hashable α] :
    Valid (empty : VerifiedHAMT.SetWithoutValArray.Raw α) :=
  wellFormed_empty _
end VerifiedHAMT.SetWithoutValArray.Raw
