-- Prove2me | solution 1 for QEC.Bounds.BPTCommutingProjectorModel.starProjection_commute_of_invariant_of_orthogonalInvariant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T13:23:54.332+00:00
-- url     : https://prove2.me/submissions/23062014-bf85-4f36-b6f9-b508d93efd70

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
    {B : Type u}
    [NormedAddCommGroup B] [InnerProductSpace Complex B] [Semantics.FiniteQuantumSystem B]
    (W : Submodule Complex B) (T : Semantics.Operator B)
    (hW : ∀ ⦃vector : B⦄, vector ∈ W → T vector ∈ W)
    (hWperp : ∀ ⦃vector : B⦄, vector ∈ Wᗮ → T vector ∈ Wᗮ) :
    Commute W.starProjection.toLinearMap T := by
  apply LinearMap.ext
  intro vector
  change W.starProjection (T vector) = T (W.starProjection vector)
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · exact hW (W.starProjection_apply_mem vector)
  · rw [← map_sub]
    exact hWperp (Submodule.sub_starProjection_mem_orthogonal vector)
end QEC.Bounds.BPTCommutingProjectorModel
