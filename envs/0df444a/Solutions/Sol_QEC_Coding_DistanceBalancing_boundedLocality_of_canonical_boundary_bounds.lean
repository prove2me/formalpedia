-- Prove2me | solution 1 for QEC.Coding.DistanceBalancing.boundedLocality_of_canonical_boundary_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:45:00.447565+00:00
-- url     : https://prove2.me/submissions/ee0b1e80-735c-4b18-8702-e23730b6c48a

import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Definitions.Def_QEC_Coding_CodeReduction_DistanceBalancing_Locality
import Theorems.Thm_QEC_QLDPC_chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.DistanceBalancing
universe u
open QEC.Coding.FiberBundle
variable {xZero xOne xTwo classicalBit classicalCheck : Type u}
variable [Fintype xZero] [DecidableEq xZero]
variable [Fintype xOne] [DecidableEq xOne]
variable [Fintype xTwo] [DecidableEq xTwo]
variable [Fintype classicalBit] [DecidableEq classicalBit]
variable [Fintype classicalCheck] [DecidableEq classicalCheck]
variable (D : Data xZero xOne xTwo classicalBit classicalCheck)
namespace QEC.Coding.DistanceBalancing
theorem _root_.solution
    {zero one two : Type u}
    [Fintype zero] [DecidableEq zero]
    [Fintype one] [DecidableEq one]
    [Fintype two] [DecidableEq two]
    (X : ChainComplexData (ZMod 2)
      (Word (ZMod 2) zero) (Word (ZMod 2) one) (Word (ZMod 2) two))
    {checkBound variableBound : Nat}
    (hZero : ∀ x0,
      HammingWeight
        (wordLinearMapTranspose X.boundary1
          (canonicalBasisWord (F := ZMod 2) x0)) ≤ checkBound)
    (hTwo : ∀ x2,
      HammingWeight
        (X.boundary2 (canonicalBasisWord (F := ZMod 2) x2)) ≤ checkBound)
    (hVariable : ∀ x1,
      ((QEC.QLDPC.chainComplexBoundaryIncidence X).variableSupport x1).card ≤
        variableBound) :
    BoundedLocality
      (QEC.QLDPC.chainComplexBoundaryIncidence X).localityProfile
      (max checkBound variableBound) := by
  classical
  apply QEC.QLDPC.chainComplexBoundaryIncidence_boundedLocality_of_boundary_bounds
    X (w := checkBound) (variableDegree := variableBound)
  · exact hZero
  · exact hTwo
  · exact hVariable
end QEC.Coding.DistanceBalancing
