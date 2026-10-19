-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockGaloisConjugatorWithCoefficient_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/36617870-f040-4b0c-bb13-06813c8eb267

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteBlockCoefficientMatrixHom_galoisLeftProduct

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (j k : Fin 3) (hjk : j ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    finiteOuterBlockGaloisConjugatorWithCoefficient W j k hjk B t ∈
      finiteOuterBlockRootSubgroup W j k hjk := by
  refine ⟨Multiplicative.ofAdd
    (finiteBlockGaloisLeftProductCoefficientMatrix W B t), ?_⟩
  change
    elementaryRootHom j k hjk
      (Multiplicative.ofAdd
        (finiteBlockCoefficientMatrixHom W
          (finiteBlockGaloisLeftProductCoefficientMatrix W B t))) =
      elementaryRootHom j k hjk
        (Multiplicative.ofAdd
          (finiteBlockGaloisMatrixOver R t *
            finiteBlockCoefficientMatrixHom W B))
  rw [finiteBlockCoefficientMatrixHom_galoisLeftProduct]
end SoficGroups
