-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.pureFactorTensorComplementProjector_eq_rankOne_mul_complementExtension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:02:41.765203+00:00
-- url     : https://prove2.me/submissions/b9571245-1f16-41ae-a4fe-80529a119190

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_Model
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Data.Finset.NoncommProd
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.SimpleModule.Isotypic
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Definitions.Def_QEC_Bounds_BPTDisentangling_InteractionAlgebra
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_quditSubsystem_extendLocalToRegister_mul_complementOperator

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
    (phi : (M.regionSubsystem region).selectedSystem)
    (complementProjector : Semantics.Operator (M.regionSubsystem region).complementSystem) :
    M.pureFactorTensorComplementProjector region phi complementProjector =
      (M.regionSubsystem region).extendLocalToRegister
        (InnerProductSpace.rankOne Complex phi phi).toLinearMap *
      ((M.regionSubsystem region).registerFactorization.symm.conjOperator
        (TensorProduct.map
          (1 : Semantics.Operator (M.regionSubsystem region).selectedSystem)
          complementProjector)) := by
  symm
  exact quditSubsystem_extendLocalToRegister_mul_complementOperator
    (M.regionSubsystem region)
    (InnerProductSpace.rankOne Complex phi phi).toLinearMap complementProjector
end QEC.Bounds.BPTCommutingProjectorModel
