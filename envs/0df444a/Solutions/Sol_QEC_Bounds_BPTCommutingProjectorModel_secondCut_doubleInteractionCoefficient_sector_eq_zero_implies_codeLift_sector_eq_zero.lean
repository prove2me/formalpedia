-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_doubleInteractionCoefficient_sector_eq_zero_implies_codeLift_sector_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:26.083723+00:00
-- url     : https://prove2.me/submissions/70155580-ec69-4fef-84e9-2f46929c7bb8

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_dichotomy
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq

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
      (M.fourFactorB region))
    (cd cd' : Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region))
    (a a' : M.fourFactorA region)
    (hnonzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' ≠ 0)
    (hzero : M.secondCutDoubleInteractionCoefficient region cd cd' a a' *
      leftIsotypicSectorProjector (M.fourFactorProjectorABLocal region) component = 0) :
    M.secondCutCodeLift region * M.secondCutSectorLift region component = 0 := by
  rcases M.secondCutCodeLift_sector_dichotomy region hM component with hcodeZero | hcodeFull
  · exact hcodeZero
  · exfalso
    have hcoefficientFull :=
      M.secondCutCodeLift_sector_eq_codeLift_implies_doubleInteractionCoefficient_eq
        region component cd cd' a a' hcodeFull
    rw [hzero] at hcoefficientFull
    exact hnonzero hcoefficientFull.symm
end QEC.Bounds.BPTCommutingProjectorModel
