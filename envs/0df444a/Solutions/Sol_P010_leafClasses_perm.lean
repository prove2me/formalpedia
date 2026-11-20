-- Prove2me | solution 1 for P010.leafClasses_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:54:25.868016+00:00
-- url     : https://prove2.me/submissions/0b32815c-1d5e-4b4d-868e-53ec30c120f9

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_leafClass_perm

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) (leaves : List ℕ)
    (hleaves : ∀ p ∈ leaves, p ∈ middlePrimes n) :
    (leaves.flatMap (fun p => [p, 2 * p])).Perm
      (classConcat n leaves) := by
  unfold classConcat
  exact List.Perm.flatMap_left leaves
    (fun p hp => leafClass_perm n p (hleaves p hp))
end P010
