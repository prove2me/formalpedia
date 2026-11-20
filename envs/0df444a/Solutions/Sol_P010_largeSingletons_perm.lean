-- Prove2me | solution 1 for P010.largeSingletons_perm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:53:45.332025+00:00
-- url     : https://prove2.me/submissions/5811058c-b7eb-4556-82ff-600868a3992a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_isolatedLargeClass_perm

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n : ℕ) :
    ((largePrimes n).toList.map (fun p => [p])).flatten.Perm
      (classConcat n (largePrimes n).toList) := by
  classical
  change ((largePrimes n).toList.flatMap (fun p => [p])).Perm
    ((largePrimes n).toList.flatMap (fun p => (primeClass n p).toList))
  apply List.Perm.flatMap_left
  intro p hp
  exact isolatedLargeClass_perm n p (Finset.mem_toList.mp hp)
end P010
