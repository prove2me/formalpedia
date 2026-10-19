-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockRoot_commutator_mem_productCentral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/5ff0de90-ccf6-4e5b-b0cd-75c2d2afddaa

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRoot_commutator

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (A B : Matrix (Fin 3) (Fin 3) W) :
    ⁅finiteOuterBlockRootHom W i j hij (Multiplicative.ofAdd A),
      finiteOuterBlockRootHom W j k hjk (Multiplicative.ofAdd B)⁆ ∈
      finiteOuterBlockProductCentralRootSubgroup W i k hik B := by
  refine ⟨Multiplicative.ofAdd A, ?_⟩
  change
    elementaryRootHom i k hik
      (Multiplicative.ofAdd
        (finiteBlockCoefficientMatrixHom W A *
          finiteBlockCoefficientMatrixHom W B)) =
      ⁅elementaryRootHom i j hij
        (Multiplicative.ofAdd (finiteBlockCoefficientMatrixHom W A)),
       elementaryRootHom j k hjk
        (Multiplicative.ofAdd (finiteBlockCoefficientMatrixHom W B))⁆
  exact (finiteOuterElementaryRoot_commutator i j k hij hjk hik
    (finiteBlockCoefficientMatrixHom W A)
    (finiteBlockCoefficientMatrixHom W B)).symm
end SoficGroups
