-- Prove2me | solution 1 for Orthogonalization.assembled_bound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:20:01.56702+00:00
-- url     : https://prove2.me/submissions/d7190022-021a-42f3-8618-a9f78e9669c4

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Assembly.lean
-/
/-
# Assembly of the orthogonalized PVM (step **F3**)

This file carries out the last step of the proof of Theorem 1.2 in the finite
case (M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 3, lines 247–271 of `manuscript/arXiv2103.14126v2.tex`;
`PLAN.md` §1, step **F3**).

The input is the isometry data of `Orthogonalization/IsometryData.lean`: reading
the partial isometry `u ∈ M_n(M)` of Lemma 3.2 block by block gives operators
`w_i = (e_{1i} ⊗ 1) u` on `H` satisfying

* (W1) `∑ i, w_i* w_i = 1`,
* (W2) `w_i w_j* = δ_{ij} q_i`,
* (W3) `w_i √y = q_i √a_i` where `y = ∑ j, q_j a_j`.

The paper's PVM is `p_i = u* t_i u` with `t_i = e_{ii} ⊗ q_i`, which in this
block notation is exactly `p_i = w_i* w_i` (`assembledPVM`). We prove:

* `IsometryData.q_mul_w`: `q_i w_i = w_i`;
* `assembledPVM_isStarProjection`, `sum_assembledPVM`: `(p_i)` is a PVM;
* `sqrt_mul_assembledPVM_mul_sqrt`: the paper's `|x| p_i |x| = q_i a_i`;
* `assembled_bound`: the three-term estimate
  `φ (∑ i, |a_i − p_i|²) < 9 ε`, from `φ (∑ a_i²) > 1 − ε` and
  `φ (∑ q_i a_i) ≥ 1 − ε`.

The estimate is proved through `assembled_bound_core`, which abstracts the
square root `|x|` into a plain operator `s` subject to the three properties the
argument actually uses (`0 ≤ s ≤ 1`, `s² = y`, `s p_i s = q_i a_i`); this keeps
the (long) inequality bookkeeping free of `CFC.sqrt`.

Nothing in this file is a statement of the paper; it is proof-side machinery for
`Orthogonalization/Basic.lean`.
-/
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/Positivity.lean
-/
/-
# Operator-order toolbox

Generic order-theoretic facts about the C⋆-algebra `H →L[ℂ] H` of bounded
operators on a complex Hilbert space, used throughout the formalization of
M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*
(arXiv:2103.14126v2).

Nothing in this file refers to POVMs, von Neumann algebras or the paper's
statements: it collects the elementary Loewner-order manipulations that the
assembly step (`PLAN.md` §1, step **F3**) and the reduction steps use over and
over:

* products of commuting positive operators (`mul_nonneg_of_commute`);
* the two operator inequalities the paper uses for `0 ≤ y ≤ 1`, namely
  `y² ≤ y` (`sq_le_self_of_le_one`) and `(1 - y)² ≤ 1 - y²`
  (`one_sub_sq_le_one_sub_sq'`);
* compressions by a projection commuting with a positive operator
  (`IsStarProjection.mul_le_of_commute`, `IsStarProjection.mul_nonneg_of_commute`);
* the continuous-functional-calculus square root: positivity, the bound
  `√y ≤ 1` for `y ≤ 1`, and the fact that it inherits every commutant
  (`Commute.sqrt`);
* positive linear functionals `φ` on `H →L[ℂ] H`, i.e. `ℂ`-linear maps with
  `0 ≤ φ (x* x)` for the `ComplexOrder` order on `ℂ`: they are monotone
  (`re_le_re_of_le`), real on positives (`im_eq_zero_of_nonneg`), and
  positive on positives (`nonneg_of_nonneg`).

The order on `H →L[ℂ] H` is the Loewner order
(`ContinuousLinearMap.le_def : f ≤ g ↔ (g - f).IsPositive`), for which Mathlib
provides a `StarOrderedRing` structure and the continuous functional calculus.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/Assembly.lean (solution of Orthogonalization.assembled_bound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.Equiv.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Star
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_PhiNorm
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Assembly
import Theorems.Thm_Orthogonalization_assembledPVM_isStarProjection
import Theorems.Thm_Orthogonalization_assembled_bound_core
import Theorems.Thm_Orthogonalization_sqrt_mul_assembledPVM_mul_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- The product of two **commuting** positive operators is positive.
(Without the commutation hypothesis this is false.) This is Mathlib's
`Commute.mul_nonneg`, restated with the hypotheses in the order in which the
proof uses them. -/
theorem mul_nonneg_of_commute (hx : 0 ≤ x) (hy : 0 ≤ y) (h : Commute x y) : 0 ≤ x * y :=
  h.mul_nonneg hx hy
end
end Orthogonalization

namespace Orthogonalization.IsStarProjection
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {q b : H →L[ℂ] H}
/-- If `q` is a projection commuting with a positive `b`, then `q b` is positive. -/
theorem mul_nonneg_of_commute (hq : IsStarProjection q) (hb : 0 ≤ b) (h : Commute q b) :
    0 ≤ q * b :=
  Orthogonalization.mul_nonneg_of_commute hq.nonneg hb h
end
end Orthogonalization.IsStarProjection

namespace Orthogonalization.IsStarProjection
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {q b : H →L[ℂ] H}
/-- If `q` is a projection commuting with a positive `b`, then `q b ≤ b`,
because `b - q b = (1 - q) b` is a product of commuting positive operators. -/
theorem mul_le_of_commute (hq : IsStarProjection q) (hb : 0 ≤ b) (h : Commute q b) :
    q * b ≤ b := by
  have hc : Commute (1 - q) b := (Commute.one_left b).sub_left h
  have h1 : 0 ≤ (1 - q) * b :=
    Orthogonalization.mul_nonneg_of_commute hq.one_sub_nonneg hb hc
  have he : (1 - q) * b = b - q * b := by noncomm_ring
  rw [he] at h1
  exact sub_nonneg.mp h1
end
end Orthogonalization.IsStarProjection

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- The square root of an operator is positive (junk value `0` if the argument
is not positive). Re-export of `CFC.sqrt_nonneg`. -/
theorem sqrt_nonneg (y : H →L[ℂ] H) : 0 ≤ CFC.sqrt y := CFC.sqrt_nonneg y
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- `√y √y = y` for `0 ≤ y`. Re-export of `CFC.sqrt_mul_sqrt_self`. -/
theorem sqrt_mul_sqrt_self (hy : 0 ≤ y) : CFC.sqrt y * CFC.sqrt y = y :=
  CFC.sqrt_mul_sqrt_self y hy
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- If `y ≤ 1` then `√y ≤ 1`, by operator monotonicity of the square root and
`√1 = 1`. (Positivity of `y` is not needed: if `y` is not positive then
`√y = 0 ≤ 1`.) -/
theorem sqrt_le_one_of_le_one (hy1 : y ≤ 1) : CFC.sqrt y ≤ 1 := by
  simpa using CFC.sqrt_le_sqrt y 1 hy1
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a q w : ι → H →L[ℂ] H}
/-- The assembled projections sum to `1`: this is (W1). -/
theorem sum_assembledPVM (hw : IsometryData a q w) : ∑ i, assembledPVM w i = 1 :=
  hw.sum_star_mul
end
end Orthogonalization

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q w : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hw : IsometryData a q w) (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - assembledPVM w i) * (a i - assembledPVM w i))).re < 9 * ε := by
  have hy0 : (0 : H →L[ℂ] H) ≤ ∑ j, q j * a j :=
    Finset.sum_nonneg fun j _ =>
      Orthogonalization.IsStarProjection.mul_nonneg_of_commute (hq j) (ha0 j) (hqa j)
  have hy1 : ∑ j, q j * a j ≤ 1 := by
    rw [← ha1]
    exact Finset.sum_le_sum fun j _ =>
      Orthogonalization.IsStarProjection.mul_le_of_commute (hq j) (ha0 j) (hqa j)
  exact assembled_bound_core φ hφ hφ1 a q (assembledPVM w) (CFC.sqrt (∑ j, q j * a j))
    ha0 ha1 hq hqa (assembledPVM_isStarProjection hw) (sum_assembledPVM hw)
    (sqrt_nonneg _) (sqrt_le_one_of_le_one hy1) (sqrt_mul_sqrt_self hy0)
    (sqrt_mul_assembledPVM_mul_sqrt hw hq hqa ha0) ε hε hlarge
end Orthogonalization
