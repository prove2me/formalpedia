-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendAlongLinearIsometryUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:12:16.392963+00:00
-- url     : https://prove2.me/submissions/5d3e8131-2ee9-44a6-aee4-5279e8873d2f

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendSubmoduleUnitary_apply_subtype

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
    {A H : Type u} [NormedAddCommGroup A] [InnerProductSpace Complex A]
    [Semantics.FiniteQuantumSystem A] [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (J : A →ₗᵢ[Complex] H)
    (U : Semantics.UnitaryTransport A A) (x : A) :
    extendAlongLinearIsometryUnitary J U (J x) = J (U x) := by
  let E : A ≃ₗᵢ[Complex] J.range := J.equivRange
  let EJ : Semantics.UnitaryTransport A J.range := unitaryTransportOfLinearIsometryEquiv E
  let Urange : Semantics.UnitaryTransport J.range J.range :=
    composeUnitaryTransport (composeUnitaryTransport EJ.symm U) EJ
  let s : J.range := E x
  have hs : (s : H) = J x := rfl
  calc
    extendAlongLinearIsometryUnitary J U (J x) =
        extendAlongLinearIsometryUnitary J U (s : H) := by rw [hs]
    _ = (Urange s : J.range) := extendSubmoduleUnitary_apply_subtype J.range Urange s
    _ = (E (U x) : J.range) := by
      have hback : EJ.symm s = x := by
        change E.symm s = x
        change E.symm (E x) = x
        exact E.symm_apply_apply x
      change J (U (EJ.symm s)) = J (U x)
      rw [hback]
    _ = J (U x) := rfl
end QEC.Bounds.BPTCommutingProjectorModel
