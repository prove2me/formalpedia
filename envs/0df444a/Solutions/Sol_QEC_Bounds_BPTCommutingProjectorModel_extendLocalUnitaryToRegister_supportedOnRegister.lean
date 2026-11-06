-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalUnitaryToRegister_supportedOnRegister
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T20:57:59.026973+00:00
-- url     : https://prove2.me/submissions/842d0e3f-ebfd-432c-bab2-3a6c900ebb56

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendLocalUnitaryToRegister_toLinearMap_eq

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
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    S.OperatorSupportedOnRegister
      (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap := by
  refine ⟨U.toLinearEquiv.toLinearMap, ?_⟩
  exact extendLocalUnitaryToRegister_toLinearMap_eq q S U
end QEC.Bounds.BPTCommutingProjectorModel
