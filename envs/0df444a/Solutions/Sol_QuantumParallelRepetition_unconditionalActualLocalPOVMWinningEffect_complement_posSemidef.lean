-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualLocalPOVMWinningEffect_complement_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:18.584171+00:00
-- url     : https://prove2.me/submissions/0059c979-1bd7-4173-9dd2-b4fdb8a6709d

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualLocalPOVMLosingEffect_posSemidef
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualLocalPOVMWinningEffect_add_losingEffect

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B s t : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    (G : Game X Y A B) (PA : POVM A s) (PB : POVM B t)
    (x : X) (y : Y) :
    (1 - directDSVActualLocalPOVMWinningEffect
      G PA PB x y).PosSemidef := by
  have complete :=
    unconditionalActualLocalPOVMWinningEffect_add_losingEffect
      G PA PB x y
  have partition :
      1 - directDSVActualLocalPOVMWinningEffect
          G PA PB x y =
        unconditionalActualLocalPOVMLosingEffect
          G PA PB x y := by
    calc
      _ =
          (directDSVActualLocalPOVMWinningEffect
              G PA PB x y +
            unconditionalActualLocalPOVMLosingEffect
              G PA PB x y) -
            directDSVActualLocalPOVMWinningEffect
              G PA PB x y := by rw [complete]
      _ = _ := by abel
  rw [partition]
  exact unconditionalActualLocalPOVMLosingEffect_posSemidef
    G PA PB x y
end QuantumParallelRepetition
