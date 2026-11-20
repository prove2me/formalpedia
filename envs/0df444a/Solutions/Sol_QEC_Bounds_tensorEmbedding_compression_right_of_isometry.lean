-- Prove2me | solution 1 for QEC.Bounds.tensorEmbedding_compression_right_of_isometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:36:40.811403+00:00
-- url     : https://prove2.me/submissions/47ec8cfc-e085-4a5d-b120-af6e19a612f4

import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_Coordinates
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion_Transport_SelectedTensorCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_linearIsometry_adjoint_comp_self
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorEmbedding_compression_right


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open scoped TensorProduct
universe u v
namespace QEC.Bounds
theorem _root_.solution
    {H K H' K' : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [Semantics.FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    [NormedAddCommGroup H'] [InnerProductSpace Complex H'] [Semantics.FiniteQuantumSystem H']
    [NormedAddCommGroup K'] [InnerProductSpace Complex K'] [Semantics.FiniteQuantumSystem K']
    (eH : H →ₗᵢ[Complex] H') (eK : K →ₗ[Complex] K')
    (B : Semantics.Operator K') :
    (LinearMap.adjoint (TensorProduct.map eH.toLinearMap eK)).comp
        ((TensorProduct.map (1 : Semantics.Operator H') B).comp
          (TensorProduct.map eH.toLinearMap eK)) =
      TensorProduct.map (1 : Semantics.Operator H)
        ((LinearMap.adjoint eK).comp (B.comp eK)) := by
  apply BPTCommutingProjectorModel.tensorEmbedding_compression_right eH.toLinearMap eK
  exact BPTCommutingProjectorModel.linearIsometry_adjoint_comp_self eH
end QEC.Bounds
