-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryRoot_commute_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/3429cb58-19dd-4be4-8ba7-ee1111337603

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
omit [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (i j : Fin 3) (hij : i ≠ j)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute
      (elementaryRootHom i j hij (Multiplicative.ofAdd A))
      (elementaryRootHom i j hij (Multiplicative.ofAdd B)) := by
  change
    elementaryRootHom i j hij (Multiplicative.ofAdd A) *
      elementaryRootHom i j hij (Multiplicative.ofAdd B) =
    elementaryRootHom i j hij (Multiplicative.ofAdd B) *
      elementaryRootHom i j hij (Multiplicative.ofAdd A)
  calc
    _ = elementaryRootHom i j hij
        (Multiplicative.ofAdd A * Multiplicative.ofAdd B) :=
      (map_mul (elementaryRootHom i j hij)
        (Multiplicative.ofAdd A) (Multiplicative.ofAdd B)).symm
    _ = elementaryRootHom i j hij
        (Multiplicative.ofAdd B * Multiplicative.ofAdd A) := by
      rw [mul_comm]
    _ = _ := map_mul (elementaryRootHom i j hij)
      (Multiplicative.ofAdd B) (Multiplicative.ofAdd A)
end SoficGroups
