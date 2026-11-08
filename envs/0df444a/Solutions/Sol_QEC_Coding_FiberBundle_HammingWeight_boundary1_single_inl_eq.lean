-- Prove2me | solution 1 for QEC.Coding.FiberBundle.HammingWeight_boundary1_single_inl_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T10:42:48.227586+00:00
-- url     : https://prove2.me/submissions/01b2a549-a92e-447b-943c-f4a97a18efd7

import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionDistance
import Definitions.Def_QEC_Coding_QLDPC_Core
import Definitions.Def_QEC_Coding_FiberBundle_WeightReductionParameters
import Theorems.Thm_QEC_Coding_FiberBundle_HammingWeight_graph_coordinate_eq

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
    (b : baseOne) (j : fiberZero) :
    HammingWeight (boundary1 D (Pi.single (Sum.inl (b, j)) 1)) =
      HammingWeight (fun a => D.baseBoundary a b) := by
  classical
  rw [boundary1_single_inl]
  exact HammingWeight_graph_coordinate_eq
    (fun a => D.baseBoundary a b)
    (fun a => (D.connection b a).onZero j)
end QEC.Coding.FiberBundle
