-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.actualProjectorSeparated_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:32:33.312636+00:00
-- url     : https://prove2.me/submissions/20adaf2b-794d-4e62-b73f-9b142ad68763

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
theorem _root_.solution
    (M : BPTCommutingProjectorModel L kappa) (left right : Finset L.Site) :
    M.ActualProjectorSeparated left right ↔
      M.ActualProjectorSeparated right left := by
  constructor
  · intro hoverlap check hboth
    exact hoverlap check ⟨hboth.2, hboth.1⟩
  · intro hoverlap check hboth
    exact hoverlap check ⟨hboth.2, hboth.1⟩
end QEC.Bounds.BPTCommutingProjectorModel
