-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.boundary2_residualLift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:48:21.90543+00:00
-- url     : https://prove2.me/submissions/b980b7ab-072f-4f89-bb09-1ab13171fbc5

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_CodeReduction_Classical_Distance
import Mathlib.LinearAlgebra.Dual.Lemmas
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Theorems.Thm_QEC_Coding_DistanceBalancing_sliceRemainder_apply_inl
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_residualLift_apply_inr
import Theorems.Thm_QEC_Coding_DistanceBalancing_boundary2_residualLift_apply_inl

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
    (S : Matrix classicalBit classicalCheck (ZMod 2))
    (hS : IsClassicalRightInverse D S)
    (z : Word (ZMod 2)
      (QubitIndex xOne xTwo classicalBit classicalCheck))
    (hz : z ∈ (chainComplex D).middleCycleCode.carrier)
    (hFill : ∀ a : classicalBit,
      xOneBitSlice z a ∈ (sourceChainComplex D).middleBoundaryCode.carrier) :
    boundary2 D (residualLift D S z hFill) = sliceRemainder D z hFill := by
  ext q
  cases q with
  | inl q =>
      rcases q with ⟨x1, a⟩
      rw [boundary2_residualLift_apply_inl D S z hz hFill x1 a]
      exact (sliceRemainder_apply_inl D z hFill x1 a).symm
  | inr q =>
      rcases q with ⟨x2, b⟩
      exact boundary2_residualLift_apply_inr D S hS z hFill x2 b
end QEC.Coding.DistanceBalancing
