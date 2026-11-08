-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_boundary1_reducedQubitBasisWord_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:38:33.360139+00:00
-- url     : https://prove2.me/submissions/6462bb26-7bd0-4d7c-9303-57e1e50ec331

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_graph_coordinate_eq
import Theorems.Thm_QEC_Coding_FiberBundle_boundary1_reducedQubitBasisWord

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
    (b : ClassicalWeightReduction.WeightReducedBit R) (i : fiberZero) :
    HammingWeight
        (boundary1 (weightReducedData D)
          (reducedQubitBasisWord D (Sum.inl (b, i)))) =
      HammingWeight
        (fun a => (weightReducedData D).baseBoundary a b) := by
  classical
  rw [boundary1_reducedQubitBasisWord D]
  change HammingWeight
      (fun p : ClassicalWeightReduction.WeightReducedCheck R × fiberZero =>
        if p.2 = ((weightReducedData D).connection b p.1).onZero i then
          (weightReducedData D).baseBoundary p.1 b else 0) = _
  exact HammingWeight_graph_coordinate_eq
    (fun a => (weightReducedData D).baseBoundary a b)
    (fun a => ((weightReducedData D).connection b a).onZero i)
end QEC.Coding.FiberBundle
