-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_transpose_boundary2_single_inr_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:44:15.496077+00:00
-- url     : https://prove2.me/submissions/a102e306-38b3-425c-b88f-6c887a851235

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_one_fiber_coordinate_eq
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
    (a : baseZero) (j : fiberOne) :
    HammingWeight
        (wordLinearMapTranspose (boundary2 D)
          (Pi.single (Sum.inr (a, j)) 1)) =
      HammingWeight (fun b => D.baseBoundary a b) := by
  classical
  rw [boundary2]
  rw [wordLinearMapTranspose_matrixToLin_single]
  change HammingWeight
      (fun p : baseOne × fiberOne =>
        if j = (D.connection p.1 a).onOne p.2 then
          D.baseBoundary a p.1 else 0) = _
  exact HammingWeight_one_fiber_coordinate_eq
    (fun b => D.baseBoundary a b)
    (fun b => (D.connection b a).onOne) j
end QEC.Coding.FiberBundle
