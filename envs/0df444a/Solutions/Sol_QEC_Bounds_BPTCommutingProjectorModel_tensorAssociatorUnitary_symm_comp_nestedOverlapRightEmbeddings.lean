-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.tensorAssociatorUnitary_symm_comp_nestedOverlapRightEmbeddings
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T14:12:39.813575+00:00
-- url     : https://prove2.me/submissions/b157f6d7-c49b-4ff5-b0df-a241279c7ceb

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
    (W N C : Type u)
    [NormedAddCommGroup W] [InnerProductSpace Complex W] [Semantics.FiniteQuantumSystem W]
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (eta : W) (c : C) :
    (tensorAssociatorUnitary W N C).symm.toLinearEquiv.toLinearMap.comp
      ((overlapLeftEmbedding W (Semantics.CompositeSystem N C) eta).comp
        (overlapRightEmbedding N C c)) =
      (overlapRightEmbedding (Semantics.CompositeSystem W N) C c).comp
        (overlapLeftEmbedding W N eta) := by
  apply LinearMap.ext
  intro vector
  rfl
end QEC.Bounds.BPTCommutingProjectorModel
