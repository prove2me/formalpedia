-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCutPhysicalSectorProjector_supportedOnRegion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T15:01:45.853203+00:00
-- url     : https://prove2.me/submissions/fb161847-d39e-4179-bf0d-c1796bdd5173

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection

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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    (M.regionSubsystem region).OperatorSupportedOnRegister
      (M.secondCutPhysicalSectorProjector region component) := by
  apply operatorSupportedOnRegister_of_subset
    (M.regionSubsystem (M.internalBoundary region)) (M.regionSubsystem region)
  · intro site hsite
    change site ∈ region
    exact (Finset.mem_inter.mp hsite).2
  · refine ⟨(M.fourFactorBCoordinateRelabel region).symm.conjOperator
      (leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component), ?_⟩
    rfl
end QEC.Bounds.BPTCommutingProjectorModel
