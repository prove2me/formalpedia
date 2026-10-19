-- Prove2me | solution 1 for SoficGroups.finiteBlockCoefficientMatrixHom_galoisLeftProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/6ddc3109-e39d-4b46-98d7-cdd235eff3a8

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (B : Matrix (Fin 3) (Fin 3) W)
    (t : finiteBlockGaloisField) :
    finiteBlockCoefficientMatrixHom W
      (finiteBlockGaloisLeftProductCoefficientMatrix W B t) =
      finiteBlockGaloisMatrixOver R t *
        finiteBlockCoefficientMatrixHom W B := by
  ext p q
  rfl
end SoficGroups
