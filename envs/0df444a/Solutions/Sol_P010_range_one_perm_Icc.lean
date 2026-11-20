-- Prove2me | solution 1 for P010.range_one_perm_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:50:44.459243+00:00
-- url     : https://prove2.me/submissions/21f5ec1c-75e0-4865-bb07-cb77bbabbd9b

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_range_one_toFinset

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) :
    (List.range' 1 n).Perm (Finset.Icc 1 n).toList := by
  classical
  apply List.perm_of_nodup_nodup_toFinset_eq
    (List.nodup_range') (Finset.nodup_toList _)
  rw [range_one_toFinset, Finset.toList_toFinset]
end P010
