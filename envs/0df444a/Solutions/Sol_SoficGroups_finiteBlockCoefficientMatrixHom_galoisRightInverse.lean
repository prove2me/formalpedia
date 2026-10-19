-- Prove2me | solution 1 for SoficGroups.finiteBlockCoefficientMatrixHom_galoisRightInverse
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/5b6b558a-5f79-413a-9ad7-87e35513b59a

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
    (A : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField) :
    finiteBlockCoefficientMatrixHom W
      (finiteBlockGaloisRightInverseCoefficientMatrix W A s t) =
      finiteBlockCoefficientMatrixHom W A *
        finiteBlockGaloisMatrixOver R (t - s)⁻¹ := by
  ext p q
  rfl
end SoficGroups
