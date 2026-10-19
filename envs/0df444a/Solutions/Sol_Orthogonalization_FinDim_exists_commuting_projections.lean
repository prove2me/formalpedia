-- Prove2me | solution 1 for Orthogonalization.FinDim.exists_commuting_projections
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:17:09.146599+00:00
-- url     : https://prove2.me/submissions/f1f7e1e0-4366-4103-ae88-9876d40c4645

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Selection.lean
-/
/-
# Step F1 in finite dimension: choosing the commuting projections (Lemma 3.1)

Lemma 3.1 of M. de la Salle, *Orthogonalization of Positive Operator Valued
Measures* (arXiv:2103.14126v2), for `M = B(H)` with `H` finite-dimensional:
given a POVM `(a i)` and a linear functional `φ` on `B(H)`, there are projections
`q i` commuting with `a i`, with `∑ tr(q i) = dim H`, and with
`φ(∑ q i a i) ≥ φ(∑ a i a i)` (real parts).

The paper proves this by Krein–Milman on the convex set of commuting
`[0,1]`-valued families with the right trace, and shows that the extreme points
are made of projections. In finite dimension the same conclusion has a purely
combinatorial proof, used here: diagonalize each `a i` in an orthonormal
eigenbasis `(b^i_k)` with eigenvalues `λ^i_k ∈ [0,1]`, so that
`φ(∑ a i a i) = ∑_{i,k} λ^i_k · c_{i,k}` with `c_{i,k} := λ^i_k φ(P^i_k)` and
`P^i_k` the rank-one eigenprojections. The weights `λ^i_k` lie in `[0,1]` and sum
to `∑ tr(a i) = tr 1 = dim H`, so the weighted sum is dominated by the sum of
the `dim H` largest values `c_{i,k}` (`exists_finset_sum_ge`: the vertices of the
hypersimplex are the `0/1` vectors). Taking `q i := ∑ P^i_k` over the selected
pairs `(i, k)` gives projections diagonal in the eigenbasis of `a i` (hence
commuting with it) with total trace `dim H` and the required inequality.

Everything here is proof-side; no statement of the paper is encoded in this file.
-/
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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Selection.lean (solution of Orthogonalization.FinDim.exists_commuting_projections);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Nat.Defs
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
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Star.Basic
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
import Mathlib.Analysis.InnerProductSpace.StarOrder
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
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
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
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Defs
import Mathlib.Logic.Pairwise
import Mathlib.Order.BooleanAlgebra.Defs
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
import Mathlib.Order.RelClasses
import Mathlib.Order.SetNotation
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination.Lemmas
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
import Theorems.Thm_Orthogonalization_FinDim_JointEigenbasis_le_one_of_lam_le_one
import Theorems.Thm_Orthogonalization_FinDim_exists_dominating_finset
import Theorems.Thm_Orthogonalization_FinDim_exists_jointEigenbasis
import Theorems.Thm_Orthogonalization_FinDim_sum_le_sum_dominating

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
theorem P_isSelfAdjoint (k : Fin (finrank ℂ H)) : IsSelfAdjoint (J.P k) :=
  (J.P_isStarProjection k).isSelfAdjoint
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
/-- Distinct rank-one spectral projections are orthogonal. -/
theorem P_mul_P {k l : Fin (finrank ℂ H)} (h : k ≠ l) : J.P k * J.P l = 0 := by
  refine J.ext_basis fun m => ?_
  rw [mul_apply_eq_comp, J.P_apply_basis]
  by_cases hlm : l = m
  · subst hlm
    simp [J.P_apply_basis, h]
  · simp [hlm]
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
/-- An operator carrying a joint eigenbasis (with real eigenvalues) is self-adjoint. -/
theorem isSelfAdjoint_fst : IsSelfAdjoint x := by
  rw [J.eq_sum_lam_P]
  refine isSelfAdjoint_sum _ fun k _ => ?_
  exact IsSelfAdjoint.smul (Complex.conj_ofReal (J.lam k)) (J.P_isSelfAdjoint k)
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
/-- The second operator of a joint eigenbasis is self-adjoint. -/
theorem isSelfAdjoint_snd : IsSelfAdjoint a := J.swap.isSelfAdjoint_fst
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
/-- A self-adjoint operator having `basis k` as an eigenvector with a real
eigenvalue commutes with the corresponding rank-one projection `P k`. -/
theorem commute_P_of_eigen {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {k : Fin (finrank ℂ H)}
    {c : ℝ} (hc : T (J.basis k) = (c : ℂ) • J.basis k) : Commute T (J.P k) := by
  have hsymm : LinearMap.IsSymmetric (T : H →ₗ[ℂ] H) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT
  ext w
  have h1 : (inner ℂ (J.basis k) (T w) : ℂ) = (c : ℂ) * inner ℂ (J.basis k) w := by
    have h2 : (inner ℂ (J.basis k) (T w) : ℂ) = inner ℂ (T (J.basis k)) w := by
      simpa using (hsymm (J.basis k) w).symm
    rw [h2, hc, inner_smul_left]
    simp
  simp only [mul_apply_eq_comp, J.P_apply, map_smul, hc, smul_smul, h1, mul_comm]
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
theorem commute_fst_P (k : Fin (finrank ℂ H)) : Commute x (J.P k) :=
  J.commute_P_of_eigen J.isSelfAdjoint_fst (J.apply_fst k)
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
theorem commute_snd_P (k : Fin (finrank ℂ H)) : Commute a (J.P k) :=
  J.commute_P_of_eigen J.isSelfAdjoint_snd (J.apply_snd k)
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
/-- The trace of `x` is the sum of its eigenvalues. -/
theorem trace_eq_sum_lam :
    LinearMap.trace ℂ H (x : H →ₗ[ℂ] H) = ∑ k, (J.lam k : ℂ) := by
  rw [LinearMap.trace_eq_sum_inner _ J.basis]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [J.apply_fst]
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

namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- If all eigenvalues of `x` are nonnegative then `0 ≤ x` in the Loewner order. -/
theorem nonneg_of_lam_nonneg (h : ∀ k, 0 ≤ J.lam k) : (0 : H →L[ℂ] H) ≤ x := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive, J.eq_sum_lam_P]
  exact J.isPositive_sum_smul_P h
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
/-- Conversely, `0 ≤ x` forces every eigenvalue of `x` to be nonnegative. -/
theorem lam_nonneg_of_nonneg (h : (0 : H →L[ℂ] H) ≤ x) (k : Fin (finrank ℂ H)) :
    0 ≤ J.lam k := by
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive x).mp h
  have h2 := hp.re_inner_nonneg_left (J.basis k)
  rw [J.apply_fst, inner_smul_left] at h2
  simpa using h2
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
/-- Conversely, `x ≤ 1` forces every eigenvalue of `x` to be at most `1`. -/
theorem lam_le_one_of_le_one (h : x ≤ (1 : H →L[ℂ] H)) (k : Fin (finrank ℂ H)) :
    J.lam k ≤ 1 := by
  have hp := (ContinuousLinearMap.le_def x 1).mp h
  have h2 := hp.re_inner_nonneg_left (J.basis k)
  rw [sub_apply, one_apply_eq_self, J.apply_fst, inner_sub_left, inner_smul_left] at h2
  simp at h2
  linarith
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
/-- `x` is in the operator interval `[0, 1]` exactly when all its eigenvalues are. -/
theorem mem_Icc_iff :
    ((0 : H →L[ℂ] H) ≤ x ∧ x ≤ (1 : H →L[ℂ] H)) ↔ ∀ k, J.lam k ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨fun h k => ⟨J.lam_nonneg_of_nonneg h.1 k, J.lam_le_one_of_le_one h.2 k⟩,
    fun h => ⟨J.nonneg_of_lam_nonneg fun k => (h k).1,
      J.le_one_of_lam_le_one fun k => (h k).2⟩⟩
end
end Orthogonalization.FinDim.JointEigenbasis

namespace Orthogonalization.FinDim
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
variable {α : Type*} [Fintype α] [DecidableEq α]
/-- **The vertices of the hypersimplex.** If `w : α → [0,1]` sums to a natural
number `n`, the weighted sum `∑ w x * c x` is dominated by the sum of `c` over some
set of exactly `n` indices. -/
theorem exists_finset_sum_ge (c w : α → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∀ x, w x ≤ 1)
    (n : ℕ) (hsum : ∑ x, w x = n) :
    ∃ S : Finset α, S.card = n ∧ ∑ x, w x * c x ≤ ∑ x ∈ S, c x := by
  have hn : n ≤ Fintype.card α := by
    have h : ∑ x, w x ≤ ∑ _x : α, (1 : ℝ) := Finset.sum_le_sum fun x _ => hw1 x
    rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h
    exact_mod_cast h
  obtain ⟨S, hS, hdom⟩ := exists_dominating_finset c n hn
  exact ⟨S, hS, sum_le_sum_dominating c w hw0 hw1 S hdom (by rw [hsum, hS])⟩
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim.JointEigenbasis
section
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
set_option linter.unusedSectionVars false
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {x a : H →L[ℂ] H} (J : JointEigenbasis x a)
include J
/-- `x P k = λ_k P k`. -/
theorem mul_P (k : Fin (finrank ℂ H)) : x * J.P k = (J.lam k : ℂ) • J.P k := by
  ext w
  simp only [mul_apply_eq_comp, J.P_apply, map_smul, J.apply_fst, smul_apply, smul_smul, mul_comm]
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
/-- `P k x = λ_k P k`. -/
theorem P_mul (k : Fin (finrank ℂ H)) : J.P k * x = (J.lam k : ℂ) • J.P k := by
  rw [← (J.commute_fst_P k).eq, J.mul_P]
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
theorem P_mul_P' (k l : Fin (finrank ℂ H)) : J.P k * J.P l = if k = l then J.P k else 0 := by
  split_ifs with h
  · subst h; exact J.P_mul_self k
  · exact J.P_mul_P h
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
/-- A sum of distinct rank-one spectral projections is a projection. -/
theorem isStarProjection_sum_P (T : Finset (Fin (finrank ℂ H))) :
    IsStarProjection (∑ k ∈ T, J.P k) := by
  refine ⟨?_, isSelfAdjoint_sum _ fun k _ => J.P_isSelfAdjoint k⟩
  show (∑ k ∈ T, J.P k) * (∑ k ∈ T, J.P k) = ∑ k ∈ T, J.P k
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [J.P_mul_P']
  rw [Finset.sum_ite_eq]
  simp [hk]
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
/-- A sum of rank-one spectral projections commutes with the second operator. -/
theorem commute_sum_P_snd (T : Finset (Fin (finrank ℂ H))) : Commute (∑ k ∈ T, J.P k) a :=
  Commute.sum_left _ _ _ fun k _ => (J.commute_snd_P k).symm
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
/-- Each rank-one spectral projection has trace `1`. -/
theorem trace_P (k : Fin (finrank ℂ H)) : LinearMap.trace ℂ H (J.P k : H →ₗ[ℂ] H) = 1 := by
  rw [LinearMap.trace_eq_sum_inner _ J.basis]
  simp only [ContinuousLinearMap.coe_coe, J.P_apply_basis]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    simp [Ne.symm hl]
  · intro h
    exact absurd (Finset.mem_univ k) h
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
/-- The trace of a sum of distinct rank-one spectral projections is their number. -/
theorem trace_sum_P (T : Finset (Fin (finrank ℂ H))) :
    LinearMap.trace ℂ H ((∑ k ∈ T, J.P k : H →L[ℂ] H) : H →ₗ[ℂ] H) = (T.card : ℂ) := by
  rw [ContinuousLinearMap.toLinearMap_sum, map_sum]
  simp [J.trace_P]
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
/-- `x * x` in the joint eigenbasis. -/
theorem mul_self_eq_sum : x * x = ∑ k, (J.lam k : ℂ) • ((J.lam k : ℂ) • J.P k) := by
  calc x * x = x * ∑ k, (J.lam k : ℂ) • J.P k := by rw [← J.eq_sum_lam_P]
    _ = ∑ k, (J.lam k : ℂ) • ((J.lam k : ℂ) • J.P k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul_comm, J.mul_P]
end
end Orthogonalization.FinDim.JointEigenbasis

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization.FinDim
open scoped BigOperators ComplexOrder InnerProductSpace
open Module
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ) (a : ι → H →L[ℂ] H)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1) :
    ∃ q : ι → H →L[ℂ] H, (∀ i, IsStarProjection (q i)) ∧ (∀ i, Commute (q i) (a i)) ∧
      ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) = (finrank ℂ H : ℂ) ∧
      (φ (∑ i, a i * a i)).re ≤ (φ (∑ i, q i * a i)).re := by
  classical
  have hsa : ∀ i, IsSelfAdjoint (a i) := fun i => IsSelfAdjoint.of_nonneg (ha0 i)
  have hJ : ∀ i, Nonempty (JointEigenbasis (a i) (a i)) := fun i =>
    exists_jointEigenbasis (hsa i) (hsa i) (Commute.refl _)
  let J : ∀ i, JointEigenbasis (a i) (a i) := fun i => Classical.choice (hJ i)
  have ha1' : ∀ i, a i ≤ 1 := fun i => by
    rw [← ha1]
    exact Finset.single_le_sum (fun j _ => ha0 j) (Finset.mem_univ i)
  -- weights (the eigenvalues) and values
  set N := finrank ℂ H with hN
  let w : ι × Fin N → ℝ := fun p => (J p.1).lam p.2
  let c : ι × Fin N → ℝ := fun p => (J p.1).lam p.2 * (φ ((J p.1).P p.2)).re
  have hw : ∀ p, w p ∈ Set.Icc (0 : ℝ) 1 := fun p =>
    ((J p.1).mem_Icc_iff.mp ⟨ha0 p.1, ha1' p.1⟩) p.2
  -- the eigenvalues sum to the dimension
  have hsum : ∑ p, w p = N := by
    have h1 : ∑ i, LinearMap.trace ℂ H (a i : H →ₗ[ℂ] H) = (N : ℂ) := by
      rw [← map_sum, ← ContinuousLinearMap.toLinearMap_sum, ha1,
        ContinuousLinearMap.toLinearMap_one, LinearMap.trace_one]
    have h2 : ∑ i, LinearMap.trace ℂ H (a i : H →ₗ[ℂ] H) = ∑ p : ι × Fin N, ((w p : ℝ) : ℂ) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun i _ => (J i).trace_eq_sum_lam
    have h3 : ((∑ p, w p : ℝ) : ℂ) = (N : ℂ) := by rw [Complex.ofReal_sum, ← h2, h1]
    exact_mod_cast h3
  obtain ⟨S, hS, hle⟩ :=
    exists_finset_sum_ge c w (fun p => (hw p).1) (fun p => (hw p).2) N hsum
  -- the selected projections
  let T : ι → Finset (Fin N) := fun i => Finset.univ.filter fun k => (i, k) ∈ S
  refine ⟨fun i => ∑ k ∈ T i, (J i).P k, fun i => (J i).isStarProjection_sum_P (T i),
    fun i => (J i).commute_sum_P_snd (T i), ?_, ?_⟩
  · -- total trace
    have hT : ∀ i, LinearMap.trace ℂ H ((∑ k ∈ T i, (J i).P k : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        ∑ k, if (i, k) ∈ S then (1 : ℂ) else 0 := fun i => by
      rw [(J i).trace_sum_P, Finset.card_filter]
      push_cast
      rfl
    simp only [hT]
    rw [← Fintype.sum_prod_type (fun p : ι × Fin N => if p ∈ S then (1 : ℂ) else 0),
      Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, hS]
  · -- the inequality
    have hA : ∀ i, (φ (a i * a i)).re = ∑ k, w (i, k) * c (i, k) := fun i => by
      rw [(J i).mul_self_eq_sum, map_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul,
        Complex.re_ofReal_mul]
    have hQ : ∀ i, (φ ((∑ k ∈ T i, (J i).P k) * a i)).re =
        ∑ k, if (i, k) ∈ S then c (i, k) else 0 := fun i => by
      rw [Finset.sum_mul, ← Finset.sum_filter]
      rw [map_sum, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(J i).P_mul, map_smul, smul_eq_mul, Complex.re_ofReal_mul]
    rw [map_sum, map_sum, Complex.re_sum, Complex.re_sum]
    simp only [hA, hQ]
    rw [← Fintype.sum_prod_type (fun p : ι × Fin N => w p * c p),
      ← Fintype.sum_prod_type (fun p : ι × Fin N => if p ∈ S then c p else 0),
      Finset.sum_ite_mem, Finset.univ_inter]
    exact hle
end Orthogonalization.FinDim
