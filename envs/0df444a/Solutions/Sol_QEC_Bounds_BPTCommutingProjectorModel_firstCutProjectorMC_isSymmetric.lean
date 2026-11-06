-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCutProjectorMC_isSymmetric
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:12:54.124588+00:00
-- url     : https://prove2.me/submissions/992dc615-a77f-4e80-9e80-9d86cc1732a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_projectorAB_mul_BC_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_normalized_fourFactorD_vector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetric_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetric_of_overlapLiftLeft
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.firstCutProjectorMC region).IsSymmetric := by
  let U := M.firstCutCoordinateTransport region
  let V := M.fourFactorTransport region
  let P := overlapLiftLeft (C := M.fourFactorD region) (M.firstCutProjectorMC region)
  have hP : U.conjOperator P =
      V.conjOperator (M.projectorAB region * M.projectorBC region) := by
    simpa [U, V, P] using
      M.firstCutCoordinateTransport_conj_firstCutProjectorMC_eq_sourceMC region
  have hsource : (M.projectorAB region * M.projectorBC region).IsSymmetric :=
    (M.projectorAB_mul_BC_isSymmetricProjection region).isSymmetric
  have hTransport : (U.conjOperator P).IsSymmetric := by
    rw [hP]
    exact (isSymmetric_conjOperator_iff V
      (M.projectorAB region * M.projectorBC region)).mpr hsource
  have hLift : P.IsSymmetric :=
    (isSymmetric_conjOperator_iff U P).mp hTransport
  rcases M.exists_normalized_fourFactorD_vector region with ⟨eta, heta⟩
  apply isSymmetric_of_overlapLiftLeft
    (A := Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (B := M.fourFactorC region) (C := M.fourFactorD region)
    (M.firstCutProjectorMC region) eta heta
  simpa [P] using hLift
