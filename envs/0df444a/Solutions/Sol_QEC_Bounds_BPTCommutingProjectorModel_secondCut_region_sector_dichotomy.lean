-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_region_sector_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:27:38.133205+00:00
-- url     : https://prove2.me/submissions/18845229-6349-4142-915b-c1967aacbce2

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutPhysicalSectorProjector_isSymmetricProjection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fullCodeProjector_commute_secondCutPhysicalSectorProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutPhysicalSectorProjector_supportedOnRegion
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_local_commutingProjection_codeSector_eq_zero_or_codeProjector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_regionErasureRecoverable_implies_noInformationOn


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
    (hM : M.RegionErasureRecoverable region)
    (component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)) :
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component = 0 ∨
    M.fullCodeProjector * M.secondCutPhysicalSectorProjector region component =
      M.fullCodeProjector := by
  have hInformation := M.regionErasureRecoverable_implies_noInformationOn region hM
  change M.codeSpace.projector * M.secondCutPhysicalSectorProjector region component = 0 ∨
    M.codeSpace.projector * M.secondCutPhysicalSectorProjector region component =
      M.codeSpace.projector
  exact local_commutingProjection_codeSector_eq_zero_or_codeProjector
    (M.regionSubsystem region) M.codeSpace hInformation
    (M.secondCutPhysicalSectorProjector_supportedOnRegion region component)
    (M.secondCutPhysicalSectorProjector_isSymmetricProjection region component)
    (M.fullCodeProjector_commute_secondCutPhysicalSectorProjector region component)
end QEC.Bounds.BPTCommutingProjectorModel
