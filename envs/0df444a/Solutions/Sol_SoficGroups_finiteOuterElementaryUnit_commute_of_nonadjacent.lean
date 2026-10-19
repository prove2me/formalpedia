-- Prove2me | solution 1 for SoficGroups.finiteOuterElementaryUnit_commute_of_nonadjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/1cf08ea1-95f4-4aa2-a79b-8a45c2c82d31

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
    (i j k l : Fin 3) (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hli : l ≠ i)
    (A B : Matrix (Fin 3) (Fin 3) R) :
    Commute (elementaryUnit i j hij A) (elementaryUnit k l hkl B) := by
  apply Units.ext
  change
    (1 + Matrix.single i j A) * (1 + Matrix.single k l B) =
      (1 + Matrix.single k l B) * (1 + Matrix.single i j A)
  have hAB : Matrix.single i j A * Matrix.single k l B = 0 :=
    Matrix.single_mul_single_of_ne (c := A) i j k hjk B
  have hBA : Matrix.single k l B * Matrix.single i j A = 0 :=
    Matrix.single_mul_single_of_ne (c := B) k l i hli A
  noncomm_ring [hAB, hBA]
end SoficGroups
