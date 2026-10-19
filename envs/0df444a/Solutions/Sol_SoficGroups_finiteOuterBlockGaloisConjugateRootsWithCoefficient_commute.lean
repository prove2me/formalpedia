-- Prove2me | solution 1 for SoficGroups.finiteOuterBlockGaloisConjugateRootsWithCoefficient_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/46c005d4-0a4f-44fb-a339-931599449814

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_finiteOuterElementaryRootConjugates_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (W : Submodule (ZMod 2) R)
    (i j k : Fin 3) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (B : Matrix (Fin 3) (Fin 3) W)
    (s t : finiteBlockGaloisField)
    (x y : elementaryGroup (Fin 3) (Matrix (Fin 3) (Fin 3) R))
    (hx : x ∈ finiteOuterBlockGaloisConjugateRootWithCoefficient
      W i j k hij hjk B s)
    (hy : y ∈ finiteOuterBlockGaloisConjugateRootWithCoefficient
      W i j k hij hjk B t) :
    Commute x y := by
  obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hx
  obtain ⟨_, ⟨C, rfl⟩, rfl⟩ := hy
  exact finiteOuterElementaryRootConjugates_commute
    i j k hij hjk hik
    (finiteBlockCoefficientMatrixHom W A.toAdd)
    (finiteBlockCoefficientMatrixHom W C.toAdd)
    (finiteBlockGaloisMatrixOver R s *
      finiteBlockCoefficientMatrixHom W B)
    (finiteBlockGaloisMatrixOver R t *
      finiteBlockCoefficientMatrixHom W B)
end SoficGroups
