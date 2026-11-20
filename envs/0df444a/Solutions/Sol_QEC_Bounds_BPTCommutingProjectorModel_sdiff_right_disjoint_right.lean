-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.sdiff_right_disjoint_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:28:11.86832+00:00
-- url     : https://prove2.me/submissions/3e9e0c9b-11d7-417b-a21d-51012ee84018

import Definitions.Def_QEC_Bounds_BPTDisentangling_SeparatedUnionBridge
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Entropy
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Separation

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution (left right : Finset L.Site) :
    Disjoint (left \ right) right := by
  rw [Finset.disjoint_left]
  intro site hleftMinus hright
  exact (Finset.mem_sdiff.mp hleftMinus).2 hright
end QEC.Bounds.BPTCommutingProjectorModel
