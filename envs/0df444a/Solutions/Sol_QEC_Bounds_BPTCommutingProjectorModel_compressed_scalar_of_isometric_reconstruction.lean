-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.compressed_scalar_of_isometric_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:04:53.797931+00:00
-- url     : https://prove2.me/submissions/f88ac08c-2a61-47a4-a2e5-23a1ed5a1b56

import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ProjectionBlock
import Definitions.Def_QEC_Bounds_BPTDisentangling_SecondCut_ScalarTransport
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_compressed_scalar_of_named_isometric_reconstruction

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
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] [NormedAddCommGroup K]
    [InnerProductSpace Complex K] [Semantics.FiniteQuantumSystem K]
    (J : H →ₗ[Complex] K) (R L : Semantics.Operator K)
    (Lsub : Semantics.Operator H) (scalar : Complex)
    (hJadj : (LinearMap.adjoint J).comp J = (1 : Semantics.Operator H))
    (hreconstruct : R = J.comp
      (((LinearMap.adjoint J).comp (R.comp J)).comp (LinearMap.adjoint J)))
    (hprobe : (LinearMap.adjoint J).comp (L.comp J) = Lsub)
    (hscalar : R * L * R = scalar • R) :
    ((LinearMap.adjoint J).comp (R.comp J)) * Lsub *
        ((LinearMap.adjoint J).comp (R.comp J)) =
      scalar • ((LinearMap.adjoint J).comp (R.comp J)) := by
  exact compressed_scalar_of_named_isometric_reconstruction
    J R L ((LinearMap.adjoint J).comp (R.comp J)) Lsub scalar hJadj
      hreconstruct hprobe hscalar
end QEC.Bounds.BPTCommutingProjectorModel
