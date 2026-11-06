-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.fourFactorTransport_conj_projectorCD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:58:38.38573+00:00
-- url     : https://prove2.me/submissions/65e25843-190d-4179-ad90-211e055feabf

import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Definitions.Def_QEC_Bounds_BPTDisentangling_FourFactor
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransport_eq_fourFactorTransportFromRegion
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_complement_eq_extendComplementToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_fourFactorTransportFromRegion_conj_extendComplementToRegister
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalToRegister_projectorCDLocal
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_composeUnitaryTransport_conjOperator


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
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site) :
    (M.fourFactorTransport region).conjOperator (M.projectorCD region) =
      M.fourFactorExtendCD region (M.fourFactorProjectorCDLocal region) := by
  rw [M.fourFactorTransport_eq_fourFactorTransportFromRegion]
  rw [← M.extendLocalToRegister_projectorCDLocal region]
  rw [M.extendLocalToRegister_complement_eq_extendComplementToRegister region]
  rw [M.fourFactorTransportFromRegion_conj_extendComplementToRegister]
  rw [fourFactorProjectorCDLocal, fourFactorCDCoordinateTransport,
    composeUnitaryTransport_conjOperator]
end QEC.Bounds.BPTCommutingProjectorModel
