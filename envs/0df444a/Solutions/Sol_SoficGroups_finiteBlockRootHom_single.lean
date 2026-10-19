-- Prove2me | solution 1 for SoficGroups.finiteBlockRootHom_single
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/03e2a73d-1ef9-4133-8dec-bcf7ffa29b7c

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
universe u
variable {R : Type u} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin 3) (a : W) :
    finiteBlockRootHom W i j hij
        (Multiplicative.ofAdd (Matrix.single p q a)) =
      elementaryUnit (finiteBlockIndex i p) (finiteBlockIndex j q)
        (finiteBlockIndex_ne_of_ne hij p q) (a : R) := by
  apply Units.ext
  change
    finiteBlockFlattenRingEquiv
      (1 + Matrix.single i j
        ((finiteBlockCoefficientMatrixHom W) (Matrix.single p q a))) =
      1 + Matrix.single (finiteBlockIndex i p) (finiteBlockIndex j q) (a : R)
  have hsingle :
      finiteBlockCoefficientMatrixHom W (Matrix.single p q a) =
        Matrix.single p q (a : R) := by
    ext k l
    by_cases hp : p = k
    · subst k
      by_cases hq : q = l
      · subst l
        simp [finiteBlockCoefficientMatrixHom]
      · simp [finiteBlockCoefficientMatrixHom, hq]
    · simp [finiteBlockCoefficientMatrixHom, hp]
  rw [hsingle]
  rw [map_add, map_one]
  congr 1
  change
    Matrix.reindex finProdFinEquiv finProdFinEquiv
      (Matrix.comp (Fin 3) (Fin 3) (Fin 3) (Fin 3) R
        (Matrix.single i j (Matrix.single p q (a : R)))) =
      Matrix.single (finiteBlockIndex i p) (finiteBlockIndex j q) (a : R)
  rw [Matrix.comp_single_single]
  ext x y
  simp [finiteBlockIndex, Matrix.reindex, Matrix.single_apply,
    Equiv.eq_symm_apply]
end SoficGroups
