-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryRoot_commute_of_nonadjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/c923b05e-2573-4716-a554-44adb76f340a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryUnit_commute_of_nonadjacent

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (elementaryRootHom i j hij (Multiplicative.ofAdd A))
      (elementaryRootHom k l hkl (Multiplicative.ofAdd B)) := by
  apply Subtype.ext
  exact (finiteOuterElementaryUnit_commute_of_nonadjacent
    i j k l hij hkl hjk hli A B).eq
end SoficGroups
