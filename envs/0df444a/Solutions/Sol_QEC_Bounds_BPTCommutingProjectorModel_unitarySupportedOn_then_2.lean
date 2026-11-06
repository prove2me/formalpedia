-- Prove2me | solution 2 for QEC.Bounds.BPTCommutingProjectorModel.unitarySupportedOn_then
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-06T00:09:09.685211+00:00
-- url     : https://prove2.me/submissions/20e0f85f-bba1-4bb0-829d-c11145133916

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

namespace QBAux

theorem extendLocalToRegister_mul {ι : Type u} [Fintype ι] [DecidableEq ι] {q : ι → Nat}
    (S : Semantics.QuditSubsystem q) (A B : Semantics.Operator S.selectedSystem) :
    S.extendLocalToRegister (A * B) = S.extendLocalToRegister A * S.extendLocalToRegister B := by
  have h : S.extendLocal (A * B) = S.extendLocal A * S.extendLocal B := by
    apply TensorProduct.ext'
    intro x y
    simp [Semantics.QuditSubsystem.extendLocal]
  unfold Semantics.QuditSubsystem.extendLocalToRegister
  rw [h, Semantics.UnitaryTransport.conjOperator_mul]

end QBAux

theorem solution
    (M : BPTCommutingProjectorModel L kappa) (region : Finset L.Site)
    {U V : Semantics.UnitaryTransport L.Register L.Register}
    (hU : M.UnitarySupportedOn region U) (hV : M.UnitarySupportedOn region V) :
    M.UnitarySupportedOn region (thenUnitary U V) := by
  obtain ⟨a, ha⟩ := hU
  obtain ⟨b, hb⟩ := hV
  refine ⟨b * a, ?_⟩
  rw [QBAux.extendLocalToRegister_mul, ha, hb]
  apply LinearMap.ext
  intro x
  rfl
