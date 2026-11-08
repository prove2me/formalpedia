-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:44:00.530007+00:00
-- url     : https://prove2.me/submissions/96a4d3cf-0a0b-473b-af95-bab636a13567

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
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
    (b : baseOne) (i : fiberZero) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inl (b, i)) 1)) =
      HammingWeight (fun j => D.fiberBoundary i j) := by
  classical
  rw [boundary2]
  rw [wordLinearMapTranspose_matrixToLin_single]
  change HammingWeight
      (fun p : baseOne × fiberOne =>
        if b = p.1 then D.fiberBoundary i p.2 else 0) = _
  exact HammingWeight_fixed_base_coordinate_eq b
    (fun j => D.fiberBoundary i j)
end QEC.Coding.FiberBundle
