-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryRoot_conjugate_by_successor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/66062e84-5bb5-4ac0-ae05-ba606b5d57d4

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commutator

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
    let x := elementaryRootHom i j hij (Multiplicative.ofAdd A)
    let y := elementaryRootHom j k hjk (Multiplicative.ofAdd B)
    let z := elementaryRootHom i k hik (Multiplicative.ofAdd (A * B))
    y * x * y⁻¹ = z⁻¹ * x := by
  dsimp
  rw [← finiteOuterElementaryRoot_commutator i j k hij hjk hik A B]
  simp only [commutatorElement_def]
  group
end SoficGroups
