-- Prove2me | solution 1 for Orthogonalization.FinDim.exists_jointEigenbasis
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:02.135982+00:00
-- url     : https://prove2.me/submissions/71362ffe-0c5e-441f-b0a1-a7d3d21e25d3

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/JointDiag.lean
-/
/-
# Joint diagonalization of two commuting self-adjoint operators (finite dimension)

Toolkit for Lemma 3.1 of M. de la Salle, *Orthogonalization of Positive Operator
Valued Measures* (arXiv:2103.14126v2), in the finite-dimensional case (`PLAN.md`
§3, tier T1a). The perturbation argument of that lemma takes a pair `(x, a)` of
commuting self-adjoint operators on a finite-dimensional complex Hilbert space
`H`, diagonalizes them simultaneously, and moves an amount `δ` of one eigenvalue
of `x` onto another, keeping the trace and the commutation with `a` and staying
inside the operator interval `[0, 1]`.

This file packages exactly that: a `JointEigenbasis x a` (an orthonormal basis of
`H` made of joint eigenvectors of `x` and `a`, with *real* eigenvalue functions
`lam` and `mu`), its existence for commuting self-adjoint operators, the rank-one
spectral projections `P k`, the spectral decomposition and trace formula, the
translation between the Loewner order on `x` and the pointwise order on `lam`,
the characterisation of the projections among such `x`, and the two eigenvalue
shifts (`shiftPair`, `shiftOne`).

Everything here is elementary and internal to the proof; no result of this file
is a statement of the paper, so it carries no fidelity-ledger entry.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/JointDiag.lean (solution of Orthogonalization.FinDim.exists_jointEigenbasis);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Algebra.NoZeroSMulDivisors.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.BigOperators
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.CompleteLattice.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Notation
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_JointDiag

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization.FinDim
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
theorem _root_.solution {x a : H →L[ℂ] H} (hx : IsSelfAdjoint x)
    (ha : IsSelfAdjoint a) (hxa : Commute x a) : Nonempty (JointEigenbasis x a) := by
  classical
  have hX : LinearMap.IsSymmetric (x : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hx
  have hA : LinearMap.IsSymmetric (a : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp ha
  have hXA : Commute (x : H →ₗ[ℂ] H) (a : H →ₗ[ℂ] H) := by
    have := congrArg (fun T : H →L[ℂ] H => (T : H →ₗ[ℂ] H)) hxa
    simpa [Commute, SemiconjBy, ContinuousLinearMap.toLinearMap_mul] using this
  -- The joint eigenspaces, indexed by the (finitely many) pairs of eigenvalues.
  set V : (End.Eigenvalues (a : H →ₗ[ℂ] H) × End.Eigenvalues (x : H →ₗ[ℂ] H)) →
      Submodule ℂ H :=
    fun i => End.eigenspace (x : H →ₗ[ℂ] H) (i.2 : ℂ) ⊓
      End.eigenspace (a : H →ₗ[ℂ] H) (i.1 : ℂ) with hV
  have hfam : OrthogonalFamily ℂ (fun i => (V i : Submodule ℂ H))
      fun i => (V i).subtypeₗᵢ := by
    have hpair :=
      (LinearMap.IsSymmetric.orthogonalFamily_eigenspace_inf_eigenspace hX hA).pairwise
    refine OrthogonalFamily.of_pairwise ?_
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ ⟨⟨p', hp'⟩, ⟨q', hq'⟩⟩ hij
    refine hpair (i := (p, q)) (j := (p', q')) ?_
    simp only [ne_eq, Prod.mk.injEq, not_and] at hij ⊢
    intro h1 h2
    exact hij (by subst h1; subst h2; rfl)
  have htop : (⨆ i, V i) = ⊤ := by
    rw [eq_top_iff,
      ← LinearMap.IsSymmetric.iSup_iSup_eigenspace_inf_eigenspace_eq_top_of_commute hX hA hXA]
    refine iSup_le fun α => iSup_le fun γ => ?_
    by_cases hα : End.HasEigenvalue (x : H →ₗ[ℂ] H) α
    · by_cases hγ : End.HasEigenvalue (a : H →ₗ[ℂ] H) γ
      · exact le_iSup V ((⟨γ, hγ⟩, ⟨α, hα⟩))
      · rw [End.hasEigenvalue_iff, not_not] at hγ
        simp [hV, hγ]
    · rw [End.hasEigenvalue_iff, not_not] at hα
      simp [hV, hα]
  have hint : DirectSum.IsInternal V := hfam.isInternal_iff.mpr (by rw [htop]; simp)
  set b : OrthonormalBasis (Fin (finrank ℂ H)) ℂ H :=
    hint.subordinateOrthonormalBasis rfl hfam with hb
  set idx : Fin (finrank ℂ H) →
      (End.Eigenvalues (a : H →ₗ[ℂ] H) × End.Eigenvalues (x : H →ₗ[ℂ] H)) :=
    fun k => hint.subordinateOrthonormalBasisIndex rfl k hfam with hidx
  have hmem : ∀ k, b k ∈ V (idx k) := fun k =>
    hint.subordinateOrthonormalBasis_subordinate (hn := rfl) k hfam
  -- The eigenvalues of a symmetric operator are real.
  have hreal : ∀ (T : H →ₗ[ℂ] H), T.IsSymmetric → ∀ μ : End.Eigenvalues T,
      ((RCLike.re (μ : ℂ) : ℝ) : ℂ) = (μ : ℂ) := fun T hT μ =>
    RCLike.conj_eq_iff_re.mp (hT.conj_eigenvalue_eq_self μ.property)
  refine ⟨{ basis := b
            lam := fun k => RCLike.re (((idx k).2 : ℂ))
            mu := fun k => RCLike.re (((idx k).1 : ℂ))
            apply_fst := fun k => ?_
            apply_snd := fun k => ?_ }⟩
  · rw [hreal _ hX]
    exact End.mem_eigenspace_iff.mp (hmem k).1
  · rw [hreal _ hA]
    exact End.mem_eigenspace_iff.mp (hmem k).2
end Orthogonalization.FinDim
