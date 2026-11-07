-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.distance_product_le_of_detectingClassicalWord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:13.223785+00:00
-- url     : https://prove2.me/submissions/94afcf05-3e3d-40a3-aa95-06aa89702d0d

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open scoped BigOperators
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    {dSource dClassical total : Nat}
    (hClassical : ClassicalDistanceAtLeast
      D.classicalBoundary dClassical)
    (w : Word (ZMod 2) classicalBit)
    (hwKernel : Matrix.toLin' D.classicalBoundary w = 0)
    (hwNonzero : w ≠ 0)
    (hwBound : dSource * HammingWeight w ≤ total) :
    dClassical * dSource ≤ total := by
  change (∀ v : Word (ZMod 2) classicalBit,
      Matrix.toLin' D.classicalBoundary v = 0 →
      v ≠ 0 → dClassical ≤ HammingWeight v) at hClassical
  have hClassicalWeight : dClassical ≤ HammingWeight w :=
    hClassical w hwKernel hwNonzero
  calc
    dClassical * dSource ≤ HammingWeight w * dSource :=
      Nat.mul_le_mul_right dSource hClassicalWeight
    _ = dSource * HammingWeight w := Nat.mul_comm _ _
    _ ≤ total := hwBound
end QEC.Coding.DistanceBalancing
