-- Prove2me | solution 1 for P010.primeClass_toList_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:48:57.626208+00:00
-- url     : https://prove2.me/submissions/55b23573-a467-4f94-8a57-9d2725fc798a

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_primeClass_disjoint

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p q : ℕ) (hpq : p ≠ q) :
    List.Disjoint (primeClass n p).toList (primeClass n q).toList := by
  apply List.disjoint_left.mpr
  intro x hx hy
  have hd := primeClass_disjoint n p q hpq
  exact (Finset.disjoint_left.mp hd)
    (Finset.mem_toList.mp hx) (Finset.mem_toList.mp hy)
end P010
