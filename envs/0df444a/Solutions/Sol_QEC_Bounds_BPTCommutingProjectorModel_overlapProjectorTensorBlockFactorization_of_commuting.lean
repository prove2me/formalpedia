-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.overlapProjectorTensorBlockFactorization_of_commuting
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:57:10.715665+00:00
-- url     : https://prove2.me/submissions/d9d61f6a-484b-4d25-b68d-9af7e8a88a0e

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
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_overlap_projector_tensor_blocks_single_sector
import Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_commuting_overlap_block_factorization

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
    {A B C : Type u}
    [NormedAddCommGroup A] [InnerProductSpace Complex A] [Semantics.FiniteQuantumSystem A]
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (P : Semantics.Operator (Semantics.CompositeSystem A B))
    (Q : Semantics.Operator (Semantics.CompositeSystem B C))
    (hselfAdjoint : LinearMap.adjoint P = P)
    (hcommute : Commute (overlapLiftLeft (C := C) P) (overlapLiftRight (A := A) Q))
    (component : isotypicComponents (leftInteractionAlgebra P) B) :
    OverlapProjectorTensorBlockFactorization P Q component := by
  rcases commuting_overlap_block_factorization P Q hselfAdjoint hcommute with ⟨_, hblocks⟩
  rcases hblocks component with ⟨n, hn, W, hW, e, _, _⟩
  letI : NeZero n := hn
  rcases overlap_projector_tensor_blocks_single_sector
    P Q hselfAdjoint hcommute component n W hW e with ⟨U, Pleft, Qright, hleft, hright⟩
  exact ⟨n, hn, W, hW, e, U, Pleft, Qright, hleft, hright⟩
end QEC.Bounds.BPTCommutingProjectorModel
