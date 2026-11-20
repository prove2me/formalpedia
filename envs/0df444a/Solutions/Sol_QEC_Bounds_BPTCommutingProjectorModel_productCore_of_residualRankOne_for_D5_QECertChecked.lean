-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.productCore_of_residualRankOne_for_D5_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:02:27.145007+00:00
-- url     : https://prove2.me/submissions/3b2dc267-f153-48b6-92d0-d414d9d1c8c5

import Definitions.Def_QEC_Import_Compact_632eef5b7c89fcab
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCoreData
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ProductFactorization
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_Fixed_ProductCore
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_exists_unitaryTransport_conj_rankOne_eq_normalized_product
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryRTensor_conj_of_two_step_factorization


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 1800000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.productCore_of_residualRankOne_for_D5_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.productCore_of_residualRankOne_for_D5_QECertStatement
  intro «L» «kappa» «compact_inst_2» «M» «region» «bcomponent» «ccomponent» «nB» «nC» «compact_inst_9» «compact_inst_10» «WB» «WC» «UB» «UC» «Pfirst» «P_D» «Qsecond» «hresidual»
  rcases hresidual with
    ⟨phi, eta, psi, hphi, hP_D, hP_D0, heta, hPeta, hpsi, hjoint,
      hcommon, hpsiRankOne⟩
  rcases exists_unitaryTransport_conj_rankOne_eq_normalized_product psi hpsi with
    ⟨n0, c0, hn0, hc0, U, hU, hconj⟩
  have hproduct :
      (unitaryRTensor U
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).conjOperator
          ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
            (WC.restrictScalars Complex)
            (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
              (M.fourFactorD region))).symm.conjOperator
            (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond)) =
        TensorProduct.map
          (InnerProductSpace.rankOne Complex
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
            (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
              (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap P_D := by
    exact unitaryRTensor_conj_of_two_step_factorization U
      ((tensorAssociatorUnitary (isotypicLiftedMultiplicity.{0} nB)
        (WC.restrictScalars Complex)
        (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} nC)
          (M.fourFactorD region))).symm.conjOperator
        (M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond))
      (leftTensorCompression phi
        (M.firstCutPleftOnSecondCutActiveSector region bcomponent WB UB
          (WC.restrictScalars Complex) Pfirst))
      (InnerProductSpace.rankOne Complex psi psi).toLinearMap
      (InnerProductSpace.rankOne Complex
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))
        (n0 ⊗ₜ[Complex] c0 : Semantics.CompositeSystem
          (isotypicLiftedMultiplicity.{0} nB) (WC.restrictScalars Complex))).toLinearMap
      P_D hcommon hpsiRankOne hconj
  exact ⟨phi, eta, psi, n0, c0, U, hphi, hP_D, hP_D0, heta, hPeta, hpsi,
    hn0, hc0, hU, hjoint, hproduct⟩
end QEC.Bounds.BPTCommutingProjectorModel
