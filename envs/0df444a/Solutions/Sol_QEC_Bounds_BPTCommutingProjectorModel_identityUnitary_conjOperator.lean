-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.identityUnitary_conjOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:42.652927+00:00
-- url     : https://prove2.me/submissions/766cb79a-b295-4f93-b127-50072d01ed06

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor

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
theorem _root_.solution (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    (A : Semantics.Operator H) :
    (identityUnitary H).conjOperator A = A := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
