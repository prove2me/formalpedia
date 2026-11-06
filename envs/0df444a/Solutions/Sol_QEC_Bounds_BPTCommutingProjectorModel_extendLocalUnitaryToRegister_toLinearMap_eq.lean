-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendLocalUnitaryToRegister_toLinearMap_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:02:27.247464+00:00
-- url     : https://prove2.me/submissions/90d5d0b5-fbb7-406d-a28c-c0be11ff8ed6

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
    (S : Semantics.QuditSubsystem q)
    (U : Semantics.UnitaryTransport S.selectedSystem S.selectedSystem) :
    (extendLocalUnitaryToRegister q S U).toLinearEquiv.toLinearMap =
      S.extendLocalToRegister U.toLinearEquiv.toLinearMap := by
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
