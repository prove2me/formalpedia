-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:16:13.336794+00:00
-- url     : https://prove2.me/submissions/a0e48108-af0e-45c9-99ca-9412bd702e1a

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_leftIsotypicSectorProjector_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorMap_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_isSymmetricProjection_conjOperator_iff
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_one_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCoordinateTransport_symm_conj_internalBoundaryLift
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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.secondCutPhysicalSectorProjector region component).IsSymmetricProjection := by
  let A := M.fourFactorA region
  let B := M.fourFactorB region
  let CD := Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)
  let P : Semantics.Operator (Semantics.CompositeSystem A B) :=
    M.fourFactorProjectorABLocal region
  let sector : Semantics.Operator B := leftIsotypicSectorProjector P component
  let H := composeUnitaryTransport (M.fourFactorTransport region)
    (M.secondCutCoordinateTransport region).symm
  let sectorLift : Semantics.Operator (Semantics.CompositeSystem
      (Semantics.CompositeSystem A B) CD) :=
    overlapLiftLeft (C := CD)
      (TensorProduct.map (1 : Semantics.Operator A) sector)
  have hsectorProjection : sector.IsSymmetricProjection := by
    simpa [sector, P] using
      leftIsotypicSectorProjector_isSymmetricProjection P component
  have hsectorLiftProjection : sectorLift.IsSymmetricProjection := by
    dsimp [sectorLift, overlapLiftLeft]
    exact tensorMap_isSymmetricProjection
      (tensorMap_isSymmetricProjection (one_isSymmetricProjection A) hsectorProjection)
      (one_isSymmetricProjection CD)
  have hHsector :
      H.conjOperator (M.secondCutPhysicalSectorProjector region component) = sectorLift := by
    change (composeUnitaryTransport (M.fourFactorTransport region)
      (M.secondCutCoordinateTransport region).symm).conjOperator
        ((M.regionSubsystem (M.internalBoundary region)).extendLocalToRegister
          ((M.fourFactorBCoordinateRelabel region).symm.conjOperator sector)) = sectorLift
    rw [composeUnitaryTransport_conjOperator]
    simpa [A, B, CD, sectorLift] using
      M.secondCutCoordinateTransport_symm_conj_internalBoundaryLift region sector
  apply (isSymmetricProjection_conjOperator_iff H
    (M.secondCutPhysicalSectorProjector region component)).mp
  rw [hHsector]
  exact hsectorLiftProjection
