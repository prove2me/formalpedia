-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.SecondCutRankOneBlockProduct.witness_norm_QECertChecked
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:59:08.427026+00:00
-- url     : https://prove2.me/submissions/479b7cbc-c489-4109-91ba-52e37baf8e17

import Definitions.Def_QEC_Import_Compact_96042a59e59da76a
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitness
import Definitions.Def_QEC_Bounds_BPTDisentangling_ScalarCompression_LeftRankOneProductWitnessNorm

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
namespace SecondCutRankOneBlockProduct
theorem _root_.QEC.QECertImportCore.proof_96042a59e59da76a
    {M : BPTCommutingProjectorModel L kappa} {region : Finset L.Site}
    {component : isotypicComponents
      (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {n : Nat} [NeZero n]
    {W : Submodule (leftInteractionAlgebra (M.fourFactorProjectorABLocal region))
      (M.fourFactorB region)}
    {U : Semantics.UnitaryTransport (component.1.restrictScalars Complex)
      (Semantics.CompositeSystem (W.restrictScalars Complex)
        (isotypicLiftedMultiplicity.{0} n))}
    {Qright : Semantics.Operator
      (Semantics.CompositeSystem (isotypicLiftedMultiplicity.{0} n)
        (Semantics.CompositeSystem (M.fourFactorC region) (M.fourFactorD region)))}
    (h : SecondCutRankOneBlockProduct (n := n) M region component W U Qright) :
    ‖SecondCutRankOneBlockProduct.witness (n := n) h‖ = 1 :=
  (Classical.choose_spec h).1
end SecondCutRankOneBlockProduct
end QEC.Bounds.BPTCommutingProjectorModel

end

universe checked_u0
theorem _root_.solution : QEC.Bounds.BPTCommutingProjectorModel.SecondCutRankOneBlockProduct.witness_norm_QECertStatement.{checked_u0} := @QEC.QECertImportCore.proof_96042a59e59da76a.{checked_u0}
