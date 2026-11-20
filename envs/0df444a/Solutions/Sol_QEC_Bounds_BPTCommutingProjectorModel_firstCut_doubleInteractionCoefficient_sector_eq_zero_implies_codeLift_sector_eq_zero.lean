-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.firstCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:36:25.610178+00:00
-- url     : https://prove2.me/submissions/1a350470-5b3a-4476-9f66-9743eaf01799

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_dichotomy_QECertChecked
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq

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
    (hC : M.RegionErasureRecoverable (M.externalBoundary region))
    (component : isotypicComponents
      (leftInteractionAlgebra (M.firstCutProjectorMC region))
      (M.fourFactorC region))
    (d d' : M.fourFactorD region)
    (a a' : Semantics.CompositeSystem (M.fourFactorA region) (M.fourFactorB region))
    (hnonzero : M.firstCutDoubleInteractionCoefficient region d d' a a' ≠ 0)
    (hzero : M.firstCutDoubleInteractionCoefficient region d d' a a' *
      leftIsotypicSectorProjector (M.firstCutProjectorMC region) component = 0) :
    M.firstCutCodeLift region * M.firstCutSectorLift region component = 0 := by
  rcases M.firstCutCodeLift_sector_dichotomy_QECertChecked region hC component with hcodeZero | hcodeFull
  · exact hcodeZero
  · exfalso
    have hcoefficientFull :=
      M.firstCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
        region component d d' a a' hcodeFull
    rw [hzero] at hcoefficientFull
    exact hnonzero hcoefficientFull.symm
end QEC.Bounds.BPTCommutingProjectorModel
