-- Prove2me | solution 1 for P010.primeClass_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T19:45:44.414522+00:00
-- url     : https://prove2.me/submissions/7f643084-57a3-4505-ab5b-65baaf95a8c9

module
public import Definitions.Def_CoprimeAdjacencies_Statement
public import Definitions.Def_CoprimeAdjacencies_CompatMaxPrimeFac
public import Definitions.Def_CoprimeAdjacencies_Proof
public import Theorems.Thm_P010_mem_primeClass

set_option autoImplicit true
@[expose] public section
public section
open P010
namespace P010
theorem _root_.solution (n p q : ℕ) (hpq : p ≠ q) :
    Disjoint (primeClass n p) (primeClass n q) := by
  apply Finset.disjoint_left.mpr
  intro m hm hn
  have h1 := (mem_primeClass.mp hm).2.2
  have h2 := (mem_primeClass.mp hn).2.2
  exact hpq (h1.symm.trans h2)
end P010
