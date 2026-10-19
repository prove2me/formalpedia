-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryRoot_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/3ffc9410-0f06-44a2-a2da-3f932776b797

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
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    ⁅elementaryRootHom i j hij (Multiplicative.ofAdd A),
      elementaryRootHom j k hjk (Multiplicative.ofAdd B)⁆ =
      elementaryRootHom i k hik (Multiplicative.ofAdd (A * B)) := by
  apply Subtype.ext
  exact elementaryUnit_commutator i j k hij hjk hik A B
end SoficGroups
