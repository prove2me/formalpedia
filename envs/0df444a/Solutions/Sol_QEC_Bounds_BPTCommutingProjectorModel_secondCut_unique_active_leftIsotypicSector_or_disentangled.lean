-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.secondCut_unique_active_leftIsotypicSector_or_disentangled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T05:42:45.990092+00:00
-- url     : https://prove2.me/submissions/47cfb79b-cf3f-45a4-8e11-77d1c201990f

import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Definitions.Def_QEC_Bounds_BPTDisentangling_Sectors_Selection
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_disentangled_of_codeSpace_carrier_eq_bot


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
    (hM : M.RegionErasureRecoverable region) :
    M.Disentangled region ∨
      ∃ component : isotypicComponents
          (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
          (M.fourFactorB region),
        M.secondCutCodeLift region * M.secondCutSectorLift region component =
            M.secondCutCodeLift region ∧
          ∀ other : isotypicComponents
              (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
              (M.fourFactorB region),
            other ≠ component →
            M.secondCutCodeLift region * M.secondCutSectorLift region other = 0 := by
  by_cases hzero : M.codeSpace.carrier = ⊥
  · exact Or.inl (M.disentangled_of_codeSpace_carrier_eq_bot region hzero)
  · exact Or.inr
      (M.secondCut_exists_unique_active_leftIsotypicSector_of_nonzero_code region hzero hM)
end QEC.Bounds.BPTCommutingProjectorModel
