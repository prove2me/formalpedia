-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.activeSectorPhysicalUnitary_apply_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:36:41.284921+00:00
-- url     : https://prove2.me/submissions/d669d258-7d05-475c-85f2-cf0b3085c5e0

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_extendAlongLinearIsometryUnitary_apply

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
    {B C WB NB WC NC : Type u} [NormedAddCommGroup B] [InnerProductSpace Complex B]
    [Semantics.FiniteQuantumSystem B] [NormedAddCommGroup C] [InnerProductSpace Complex C]
    [Semantics.FiniteQuantumSystem C] [NormedAddCommGroup WB] [InnerProductSpace Complex WB]
    [Semantics.FiniteQuantumSystem WB] [NormedAddCommGroup NB] [InnerProductSpace Complex NB]
    [Semantics.FiniteQuantumSystem NB] [NormedAddCommGroup WC] [InnerProductSpace Complex WC]
    [Semantics.FiniteQuantumSystem WC] [NormedAddCommGroup NC] [InnerProductSpace Complex NC]
    [Semantics.FiniteQuantumSystem NC] (SB : Submodule Complex B) (SC : Submodule Complex C)
    (UB : Semantics.UnitaryTransport SB (Semantics.CompositeSystem WB NB))
    (UC : Semantics.UnitaryTransport SC (Semantics.CompositeSystem WC NC))
    (U : Semantics.UnitaryTransport (Semantics.CompositeSystem NB WC)
      (Semantics.CompositeSystem NB WC)) (x : Semantics.CompositeSystem SB SC) :
    activeSectorPhysicalUnitary SB SC UB UC U
        (submoduleTensorEmbedding SB SC x) =
      submoduleTensorEmbedding SB SC
        (conjugateUnitaryTransport (activeSectorCoordinateTransport SB SC UB UC)
          (unitaryLTensor WB (unitaryRTensor U NC)) x) := by
  exact extendAlongLinearIsometryUnitary_apply (submoduleTensorEmbedding SB SC)
    (conjugateUnitaryTransport (activeSectorCoordinateTransport SB SC UB UC)
      (unitaryLTensor WB (unitaryRTensor U NC))) x
end QEC.Bounds.BPTCommutingProjectorModel
