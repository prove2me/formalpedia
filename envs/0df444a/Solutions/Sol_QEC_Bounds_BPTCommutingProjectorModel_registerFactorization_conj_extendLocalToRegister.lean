-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.registerFactorization_conj_extendLocalToRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:58:04.126591+00:00
-- url     : https://prove2.me/submissions/56916def-de3c-41d1-887f-62d266746dbe

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
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q) (P : Semantics.Operator S.selectedSystem) :
    S.registerFactorization.conjOperator (S.extendLocalToRegister P) =
      TensorProduct.map P (1 : Semantics.Operator S.complementSystem) := by
  unfold Semantics.QuditSubsystem.extendLocalToRegister
    Semantics.QuditSubsystem.extendLocal
  rw [S.registerFactorization.conjOperator_symm_conjOperator]
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
