-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalUnitaryToRegister_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:15.290193+00:00
-- url     : https://prove2.me/submissions/a6d894fa-ec88-4e37-89a0-c400cd2b7878

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

theorem solution
    {ι : Type u} [Fintype ι] [DecidableEq ι] (q : ι → Nat)
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    S.OperatorSupportedOnRegister
      (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap := by
  refine ⟨U.toLinearEquiv.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  have key : ∀ y, (unitaryRTensor U S.complementSystem).toLinearEquiv y =
      TensorProduct.map U.toLinearEquiv.toLinearMap
        (LinearMap.id : S.complementSystem →ₗ[Complex] S.complementSystem) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  change S.registerFactorization.symm.toLinearEquiv
      (S.extendLocal U.toLinearEquiv.toLinearMap (S.registerFactorization.toLinearEquiv x)) =
    S.registerFactorization.symm.toLinearEquiv
      ((unitaryRTensor U S.complementSystem).toLinearEquiv
        (S.registerFactorization.toLinearEquiv x))
  rw [key]
  rfl
