-- Prove2me | solution 1 for P010.orderedPrimeClass_last
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:29:36.903649+00:00
-- url     : https://prove2.me/submissions/eb2e4142-e079-4bd7-9643-4d4e02063167

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p u v : ℕ) :
    (orderedPrimeClass n p u v).getLast? = some v := by
  change ((u :: (((primeClass n p).erase u).erase v).toList) ++ [v]).getLast? =
    some v
  rw [List.getLast?_append_cons]
  rfl
end P010
