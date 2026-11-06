-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.extendSubmoduleUnitary_apply_subtype
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:09:31.184804+00:00
-- url     : https://prove2.me/submissions/471695f5-dfd1-4545-9169-6d2c6ee9e540

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
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [Semantics.FiniteQuantumSystem H] (S : Submodule Complex H)
    (U : Semantics.UnitaryTransport S S) (s : S) :
    extendSubmoduleUnitary S U (s : H) = (U s : S) := by
  let L : S →ₗᵢ[Complex] H := S.subtypeₗᵢ.comp U.toLinearIsometryEquiv.toLinearIsometry
  let T : H →ₗᵢ[Complex] H := L.extend
  have hTsurj : Function.Surjective T := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := Complex)
      (V := H) (V₂ := H) rfl).mp T.injective
  let E : H ≃ₗᵢ[Complex] H := LinearIsometryEquiv.ofSurjective T hTsurj
  change E (s : H) = (U s : S)
  calc
    E (s : H) = T (s : H) := rfl
    _ = L s := by rw [← LinearIsometry.extend_apply L s]
    _ = (U s : S) := rfl
end QEC.Bounds.BPTCommutingProjectorModel
