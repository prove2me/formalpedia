-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:40:50.301856+00:00
-- url     : https://prove2.me/submissions/d38bd8d5-8cac-40a7-a664-cc2ebc5c7405

import Definitions.Def_QEC_Import_Compact_14db0e3b921ce977
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Aggregate
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Regrouping
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_tensorAssociatorUnitary_symm_conj_tensorMap
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_unitaryTransport_conj_scalar_compression



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]
set_option maxHeartbeats 4000000
namespace QEC.Bounds.BPTCommutingProjectorModel
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions_QECertStatement.{v} := by
  unfold QEC.Bounds.BPTCommutingProjectorModel.regroup_actual_active_sector_scalar_compressions_QECertStatement
  intro L kappa instKappa M region ccomponent nC nB instC instB WC UC Qsecond hrawInternal hrawExternal
  let N := isotypicLiftedMultiplicity.{0} nB
  let NC := isotypicLiftedMultiplicity.{0} nC
  let C' := WC.restrictScalars Complex
  let D' := Semantics.CompositeSystem NC (M.fourFactorD region)
  let Qprime : Semantics.Operator (Semantics.CompositeSystem N (Semantics.CompositeSystem C' D')) :=
    M.secondCutQrightOnFirstCutActiveSector region ccomponent WC UC Qsecond
  change RegroupedTwoFactorScalarCompressions Qprime
  constructor
  · intro X
    rcases hrawInternal X with ⟨scalar, hscalar⟩
    refine ⟨scalar, ?_⟩
    change Qprime * TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C')
          (TensorProduct.map (1 : Semantics.Operator NC)
            (1 : Semantics.Operator (M.fourFactorD region)))) *
        Qprime = scalar • Qprime at hscalar
    have hscalar' : Qprime * TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C') (1 : Semantics.Operator D')) *
        Qprime = scalar • Qprime := by
      simpa only [D', TensorProduct.map_one] using hscalar
    have htransport := unitaryTransport_conj_scalar_compression
      (tensorAssociatorUnitary N C' D').symm Qprime
      (TensorProduct.map X
        (TensorProduct.map (1 : Semantics.Operator C') (1 : Semantics.Operator D')))
      scalar hscalar'
    rw [tensorAssociatorUnitary_symm_conj_tensorMap] at htransport
    exact htransport
  · intro Y
    rcases hrawExternal Y with ⟨scalar, hscalar⟩
    refine ⟨scalar, ?_⟩
    change Qprime * TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y
          (TensorProduct.map (1 : Semantics.Operator NC)
            (1 : Semantics.Operator (M.fourFactorD region)))) *
        Qprime = scalar • Qprime at hscalar
    have hscalar' : Qprime * TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y (1 : Semantics.Operator D')) * Qprime = scalar • Qprime := by
      simpa only [D', TensorProduct.map_one] using hscalar
    have htransport := unitaryTransport_conj_scalar_compression
      (tensorAssociatorUnitary N C' D').symm Qprime
      (TensorProduct.map (1 : Semantics.Operator N)
        (TensorProduct.map Y (1 : Semantics.Operator D'))) scalar hscalar'
    rw [tensorAssociatorUnitary_symm_conj_tensorMap] at htransport
    exact htransport
end QEC.Bounds.BPTCommutingProjectorModel
