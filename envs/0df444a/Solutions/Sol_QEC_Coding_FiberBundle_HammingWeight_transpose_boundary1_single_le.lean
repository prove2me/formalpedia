-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary1_single_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:37:28.34956+00:00
-- url     : https://prove2.me/submissions/f0fa72c9-4ea8-4945-a010-862a716df9e4

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_sum_elim_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_fixed_base_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_wordLinearMapTranspose_matrixToLin_single

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.FiberBundle
open scoped BigOperators
universe u v
variable {baseZero baseOne fiberZero fiberOne : Type u}
variable [Fintype baseZero] [DecidableEq baseZero]
variable [Fintype baseOne] [DecidableEq baseOne]
variable [Fintype fiberZero] [DecidableEq fiberZero]
variable [Fintype fiberOne] [DecidableEq fiberOne]
variable (D : Data baseZero baseOne fiberZero fiberOne)
local notation "R" => baseSupportRelation D
namespace QEC.Coding.FiberBundle
theorem _root_.solution
    {B F : Nat}
    (a : baseZero) (i : fiberZero)
    (hBase : HammingWeight (fun b => D.baseBoundary a b) ≤ B)
    (hFiber : HammingWeight (fun j => D.fiberBoundary i j) ≤ F) :
    HammingWeight
        (wordLinearMapTranspose (boundary1 D) (Pi.single (a, i) 1)) ≤
      B + F := by
  classical
  rw [boundary1]
  rw [wordLinearMapTranspose_matrixToLin_single]
  have hBlocks :
      (fun c => boundary1Matrix D (a, i) c) =
      Sum.elim
        (fun p : baseOne × fiberZero =>
          if i = (D.connection p.1 a).onZero p.2 then
            D.baseBoundary a p.1 else 0)
        (fun p : baseZero × fiberOne =>
          if a = p.1 then D.fiberBoundary i p.2 else 0) := by
    ext c
    cases c <;> rfl
  rw [hBlocks]
  rw [HammingWeight_sum_elim_eq]
  have hHorizontal :
      HammingWeight
          (fun p : baseOne × fiberZero =>
            if i = (D.connection p.1 a).onZero p.2 then
              D.baseBoundary a p.1 else 0) =
        HammingWeight (fun b => D.baseBoundary a b) :=
    HammingWeight_one_fiber_coordinate_eq
      (fun b => D.baseBoundary a b)
      (fun b => (D.connection b a).onZero) i
  have hVertical :
      HammingWeight
          (fun p : baseZero × fiberOne =>
            if a = p.1 then D.fiberBoundary i p.2 else 0) =
        HammingWeight (fun j => D.fiberBoundary i j) :=
    HammingWeight_fixed_base_coordinate_eq a
      (fun j => D.fiberBoundary i j)
  rw [hHorizontal, hVertical]
  omega
end QEC.Coding.FiberBundle
