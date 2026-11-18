-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.rankOneTensorOperator_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-18T04:19:00.371997+00:00
-- url     : https://prove2.me/submissions/a3da1c3c-a706-43b7-b4b0-ad25142aa9fb

import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_Embeddings
import Definitions.Def_QEC_Bounds_BPTDisentangling_Assembly_AssemblyHelpers
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_isSymmetricProjection


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
    {H K : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (v : H) (hv : ‖v‖ = 1) (P : Semantics.Operator K)
    (hP : P.IsSymmetricProjection) :
    (rankOneTensorOperator v P).IsSymmetricProjection := by
  exact tensorMap_isSymmetricProjection
    (InnerProductSpace.isSymmetricProjection_rankOne_self (𝕜 := Complex) hv) hP
end QEC.Bounds.BPTCommutingProjectorModel
