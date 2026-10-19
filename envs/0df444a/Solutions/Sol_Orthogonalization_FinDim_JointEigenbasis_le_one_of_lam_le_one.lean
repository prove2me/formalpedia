-- Prove2me | solution 1 for Orthogonalization.FinDim.JointEigenbasis.le_one_of_lam_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:04.229021+00:00
-- url     : https://prove2.me/submissions/1d83c105-94d1-488e-aa37-c0d73aea684d

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/JointDiag.lean (solution of Orthogonalization.FinDim.JointEigenbasis.le_one_of_lam_le_one);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- Two continuous operators agreeing on the joint eigenbasis are equal. -/
theorem ext_basis {S T : H →L[ℂ] H} (h : ∀ k, S (J.basis k) = T (J.basis k)) : S = T := by
  ext w
  rw [← J.basis.sum_repr' w]
  simp only [map_sum, map_smul, h]
end
end Orthogonalization.FinDim.JointEigenbasis

namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- The rank-one spectral projections form a resolution of the identity. -/
theorem sum_P : ∑ k, J.P k = 1 := by
  refine J.ext_basis fun l => ?_
  rw [sum_apply ..]
  simp [J.P_apply_basis]
end
end Orthogonalization.FinDim.JointEigenbasis

namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- The spectral decomposition of `x` in its joint eigenbasis. -/
theorem eq_sum_lam_P : x = ∑ k, (J.lam k : ℂ) • J.P k := by
  refine J.ext_basis fun l => ?_
  rw [sum_apply .., J.apply_fst]
  simp [J.P_apply_basis]
end
end Orthogonalization.FinDim.JointEigenbasis

namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- A nonnegative combination of the rank-one spectral projections is a positive
operator. -/
theorem isPositive_sum_smul_P {c : Fin (finrank ℂ H) → ℝ} (hc : ∀ k, 0 ≤ c k) :
    (∑ k, (c k : ℂ) • J.P k).IsPositive := by
  refine ContinuousLinearMap.isPositive_sum _ fun k _ => ?_
  exact (ContinuousLinearMap.IsPositive.of_isStarProjection
    (J.P_isStarProjection k)).smul_of_nonneg (by exact_mod_cast hc k)
end
end Orthogonalization.FinDim.JointEigenbasis

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization.FinDim.JointEigenbasis
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
theorem _root_.solution (h : ∀ k, J.lam k ≤ 1) : x ≤ (1 : H →L[ℂ] H) := by
  rw [ContinuousLinearMap.le_def]
  have hrw : (1 : H →L[ℂ] H) - x = ∑ k, ((1 - J.lam k : ℝ) : ℂ) • J.P k := by
    have h1 : (∑ k, ((1 - J.lam k : ℝ) : ℂ) • J.P k)
        = (∑ k, J.P k) - ∑ k, (J.lam k : ℂ) • J.P k := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      module
    rw [h1, J.sum_P, ← J.eq_sum_lam_P]
  rw [hrw]
  exact J.isPositive_sum_smul_P fun k => by linarith [h k]
end Orthogonalization.FinDim.JointEigenbasis
