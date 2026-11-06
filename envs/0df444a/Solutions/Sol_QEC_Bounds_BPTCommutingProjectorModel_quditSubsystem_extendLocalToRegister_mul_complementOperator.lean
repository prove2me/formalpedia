-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.quditSubsystem_extendLocalToRegister_mul_complementOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:43:05.270122+00:00
-- url     : https://prove2.me/submissions/1aaa5170-ead4-4571-884a-a23ff84e64b8

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
import Theorems.Thm_QEC_Semantics_UnitaryTransport_conjOperator_comp


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
    (S : Semantics.QuditSubsystem L.localDimension)
    (A : Semantics.Operator S.selectedSystem) (P : Semantics.Operator S.complementSystem) :
    S.extendLocalToRegister A *
        (S.registerFactorization.symm.conjOperator
          (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)) =
      S.registerFactorization.symm.conjOperator (TensorProduct.map A P) := by
  change (S.extendLocalToRegister A).comp
      (S.registerFactorization.symm.conjOperator
        (TensorProduct.map (1 : Semantics.Operator S.selectedSystem) P)) = _
  unfold Semantics.QuditSubsystem.extendLocalToRegister Semantics.QuditSubsystem.extendLocal
  rw [← S.registerFactorization.symm.conjOperator_comp]
  rw [← TensorProduct.map_comp]
  rw [Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp]
end QEC.Bounds.BPTCommutingProjectorModel
