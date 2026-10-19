-- Prove2me | solution 1 for Orthogonalization.assembled_bound_core
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:19:05.082202+00:00
-- url     : https://prove2.me/submissions/7e76f893-92b5-4805-b40c-0930856f27c6

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
/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/PhiNorm.lean
-/
/-
# The seminorm `‖·‖_φ` of a positive functional, and its triangle inequality

For a positive linear functional `φ` on `H →L[ℂ] H` the paper
(M. de la Salle, *Orthogonalization of Positive Operator Valued Measures*,
arXiv:2103.14126v2, Section 1) writes `‖b‖_φ = √(φ (b* b))`, and the assembly
step (`PLAN.md` §1, step **F3**) applies its triangle inequality to *tuples*
`(b_i)_{i ∈ ι}`, i.e. to the norm of `PiLp 2` over the GNS space:

`‖(b_i)‖_φ = √(∑ i, φ (b_i* b_i))`.

This file defines the square of that quantity, `phiNormSq φ b`, as a real
number, and proves what the three-term estimate of step **F3** needs:

* `norm_map_star_mul_le` / `sq_norm_map_star_mul_le`: the Cauchy–Schwarz
  inequality for a positive functional, obtained from Mathlib's GNS
  construction (`PositiveLinearMap.PreGNS`), which turns `x, y ↦ φ (x* y)`
  into an honest (semi-definite) inner product;
* `phiNormSq_nonneg`, `phiNormSq_add_le`: the triangle inequality
  `√(phiNormSq φ (b + c)) ≤ √(phiNormSq φ b) + √(phiNormSq φ c)`;
* `phiNormSq_add_add_lt`: the three-term corollary
  `phiNormSq φ b ≤ ε`, `phiNormSq φ c ≤ ε`, `phiNormSq φ d < ε`
  imply `phiNormSq φ (b + c + d) < 9 ε`, which is exactly the shape in which
  the constant `9` of Theorem 1.2 is produced.

Positivity of `φ` is kept as a bare hypothesis
`hφ : ∀ z, 0 ≤ φ (star z * z)` (with the `ComplexOrder` order on `ℂ`) rather
than bundled, so that the lemmas apply verbatim to the functional underlying a
normal state.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/Assembly.lean (solution of Orthogonalization.assembled_bound_core);
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
import Theorems.Thm_Orthogonalization_phiNormSq_add_add_lt

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

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- If `0 ≤ x ≤ 1` then `x² ≤ x`: indeed `x - x² = x (1 - x)` is a product of
commuting positive operators. -/
theorem sq_le_self_of_le_one (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x * x ≤ x := by
  have hc : Commute x (1 - x) := (Commute.one_right x).sub_right (Commute.refl x)
  have h : 0 ≤ x * (1 - x) := mul_nonneg_of_commute hx0 (sub_nonneg.mpr hx1) hc
  have he : x * (1 - x) = x - x * x := by noncomm_ring
  rw [he] at h
  exact sub_nonneg.mp h
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- If `0 ≤ s ≤ 1` then `(1 - s)² ≤ 1 - s²`, because
`(1 - s²) - (1 - s)² = 2 (s - s²) = 2 s (1 - s) ≥ 0`.
This is the operator inequality used in the assembly step of the paper. -/
theorem one_sub_sq_le_one_sub_sq' {s : H →L[ℂ] H} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) * (1 - s) ≤ 1 - s * s := by
  have h : 0 ≤ s - s * s := sub_nonneg.mpr (sq_le_self_of_le_one hs0 hs1)
  have key : (1 - s * s) - (1 - s) * (1 - s) = (s - s * s) + (s - s * s) := by noncomm_ring
  refine sub_nonneg.mp ?_
  rw [key]
  exact add_nonneg h h
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {x y : H →L[ℂ] H}
/-- Conjugation by a fixed operator is monotone for the Loewner order. -/
theorem conj_le_conj (h : x ≤ y) (c : H →L[ℂ] H) : star c * x * c ≤ star c * y * c :=
  star_left_conjugate_le_conjugate h c
end
end Orthogonalization

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
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
/-- The real part of a positive functional is monotone for the Loewner order. -/
theorem re_le_re_of_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {x y : H →L[ℂ] H}
    (hxy : x ≤ y) : (φ x).re ≤ (φ y).re := by
  have h := nonneg_of_nonneg hφ (sub_nonneg.mpr hxy)
  rw [map_sub] at h
  have := (Complex.nonneg_iff.mp h).1
  simpa using this
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]
/-- `phiNormSq` is the real part of `φ` applied to the single operator
`∑ i, b_i* b_i`; this is the form in which the conclusion of Theorem 1.2 is
stated. -/
theorem phiNormSq_eq_re_map_sum (b : ι → H →L[ℂ] H) :
    phiNormSq φ b = (φ (∑ i, star (b i) * b i)).re := by
  rw [phiNormSq_def, map_sum, Complex.re_sum]
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
/-- Monotonicity of the compression by a projection commuting with the
difference: if `u ≤ v`, `r` is a projection and `r` commutes with `v - u`, then
`r u ≤ r v`, because `r (v - u)` is a product of commuting positive operators. -/
theorem IsStarProjection.mul_le_mul_of_commute (hr : IsStarProjection r) {u v : H →L[ℂ] H}
    (huv : u ≤ v) (h : Commute r (v - u)) : r * u ≤ r * v := by
  have h0 : 0 ≤ r * (v - u) :=
    Orthogonalization.mul_nonneg_of_commute hr.nonneg (sub_nonneg.mpr huv) h
  have he : r * (v - u) = r * v - r * u := by noncomm_ring
  rw [he] at h0
  exact sub_nonneg.mp h0
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
/-- `(r x)* (r x) = r x²` for a projection `r` commuting with a self-adjoint `x`.
This is the first term of the paper's decomposition, with `r = 1 - q_i`. -/
theorem star_mul_self_proj_mul (hr : IsStarProjection r) (hx : IsSelfAdjoint x)
    (h : Commute r x) : star (r * x) * (r * x) = r * (x * x) := by
  have h1 : star (r * x) = x * r := by
    rw [star_mul, hr.isSelfAdjoint.star_eq, hx.star_eq]
  rw [h1]
  calc x * r * (r * x) = x * (r * r) * x := by noncomm_ring
    _ = x * r * x := by rw [hr.isIdempotentElem.eq]
    _ = r * x * x := by rw [← h.eq]
    _ = r * (x * x) := mul_assoc _ _ _
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
/-- `(p (s - 1))* (p (s - 1)) = (1 - s) p (1 - s)` for a projection `p` and a
self-adjoint `s`. This is the third term of the paper's decomposition. -/
theorem star_mul_self_proj_mul_sub_self {p : H →L[ℂ] H} (hp : IsStarProjection p)
    (hs : star s = s) : star (p * s - p) * (p * s - p) = (1 - s) * p * (1 - s) := by
  have h1 : p * s - p = p * (s - 1) := by noncomm_ring
  rw [h1, star_mul, star_sub, hs, star_one, hp.isSelfAdjoint.star_eq]
  calc (s - 1) * p * (p * (s - 1)) = (s - 1) * (p * p) * (s - 1) := by noncomm_ring
    _ = (s - 1) * p * (s - 1) := by rw [hp.isIdempotentElem.eq]
    _ = (1 - s) * p * (1 - s) := by noncomm_ring
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
/-- `((s - 1) x)* ((s - 1) x) = x* (1 - s)² x` for a self-adjoint `s`; the
conjugating element of the second term of the paper's decomposition. -/
theorem star_mul_self_sub_one_mul (hs : star s = s) (x : H →L[ℂ] H) :
    star ((s - 1) * x) * ((s - 1) * x) = star x * ((1 - s) * (1 - s)) * x := by
  rw [star_mul, star_sub, hs, star_one]
  noncomm_ring
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
omit [CompleteSpace H] in
/-- With `s p s = z` and `p` idempotent: `s p (1 - s²) p s = z - z²`. This is
the paper's `|x| p_i (1 - |x|²) p_i |x| = |x| p_i |x| - (|x| p_i |x|)²`. -/
theorem conj_one_sub_sq_eq {p : H →L[ℂ] H} (hp : p * p = p) (hps : s * p * s = z) :
    s * p * (1 - s * s) * (p * s) = z - z * z := by
  have expand : s * p * (1 - s * s) * (p * s)
      = s * (p * p) * s - s * p * s * (s * p * s) := by noncomm_ring
  rw [expand, hp, hps]
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {r x s z : H →L[ℂ] H}
/-- `q x - (q x)² = q (x - x²)` for a projection `q` commuting with `x`. -/
theorem proj_mul_sub_sq {qq : H →L[ℂ] H} (hq : IsStarProjection qq) (h : Commute qq x) :
    qq * x - qq * x * (qq * x) = qq * (x - x * x) := by
  have h1 : qq * x * (qq * x) = qq * (x * x) := by
    calc qq * x * (qq * x) = qq * (x * qq) * x := by noncomm_ring
      _ = qq * (qq * x) * x := by rw [h.eq]
      _ = qq * qq * (x * x) := by noncomm_ring
      _ = qq * (x * x) := by rw [hq.isIdempotentElem.eq]
  rw [h1]
  noncomm_ring
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
/-- If the operator `∑ i, b_i* b_i` is dominated by `x`, then the squared
seminorm `‖(b_i)‖_φ²` is dominated by `φ x` (real parts): the real part of a
positive functional is monotone. -/
theorem phiNormSq_le_re_map_of_le {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
    (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) {ι : Type*} [Fintype ι]
    {b : ι → H →L[ℂ] H} {x : H →L[ℂ] H} (h : ∑ i, star (b i) * b i ≤ x) :
    phiNormSq φ b ≤ (φ x).re := by
  rw [phiNormSq_eq_re_map_sum]
  exact re_le_re_of_le hφ h
end
end Orthogonalization

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι] in
theorem _root_.solution (φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ)
    (hφ : ∀ x : H →L[ℂ] H, 0 ≤ φ (star x * x)) (hφ1 : φ 1 = 1)
    (a q p : ι → H →L[ℂ] H) (s : H →L[ℂ] H)
    (ha0 : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (hp : ∀ i, IsStarProjection (p i)) (hpsum : ∑ i, p i = 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hss : s * s = ∑ j, q j * a j)
    (hsp : ∀ i, s * p i * s = q i * a i)
    (ε : ℝ) (hε : 1 - ε < (φ (∑ i, a i * a i)).re)
    (hlarge : 1 - ε ≤ (φ (∑ i, q i * a i)).re) :
    (φ (∑ i, star (a i - p i) * (a i - p i))).re < 9 * ε := by
  -- Elementary consequences of the hypotheses.
  have hone : (φ (1 : H →L[ℂ] H)).re = 1 := by rw [hφ1]; simp
  have hsa : star s = s := IsSelfAdjoint.of_nonneg hs0
  have ha_le_one : ∀ i, a i ≤ 1 := by
    intro i
    rw [← ha1]
    exact Finset.single_le_sum (f := a) (fun j _ => ha0 j) (Finset.mem_univ i)
  have haa : ∀ i, a i * a i ≤ a i := fun i => sq_le_self_of_le_one (ha0 i) (ha_le_one i)
  have hsum_aa_le : ∑ i, a i * a i ≤ 1 := by
    rw [← ha1]; exact Finset.sum_le_sum fun i _ => haa i
  have hbound_aa : (φ (∑ i, a i * a i)).re ≤ 1 := by
    have h := re_le_re_of_le hφ hsum_aa_le
    rwa [hone] at h
  have hε0 : 0 < ε := by linarith
  -- Values of `φ` on the two operators that appear as bounds.
  have hval_y : (φ (1 - ∑ i, q i * a i)).re = 1 - (φ (∑ i, q i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  have hval_aa : (φ (1 - ∑ i, a i * a i)).re = 1 - (φ (∑ i, a i * a i)).re := by
    rw [map_sub, Complex.sub_re, hone]
  -- The first term `b_i = (1 - q_i) a_i`.
  have hb_op : ∀ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ (1 - q i) * a i := by
    intro i
    have hr : IsStarProjection (1 - q i) := (hq i).one_sub
    have hcr : Commute (1 - q i) (a i) := (Commute.one_left (a i)).sub_left (hqa i)
    rw [star_mul_self_proj_mul hr (IsSelfAdjoint.of_nonneg (ha0 i)) hcr]
    exact Orthogonalization.IsStarProjection.mul_le_mul_of_commute hr (haa i)
      (hcr.sub_right (hcr.mul_right hcr))
  have hb_sum : ∑ i, (1 - q i) * a i = 1 - ∑ i, q i * a i := by
    simp only [sub_mul, one_mul]
    rw [Finset.sum_sub_distrib, ha1]
  have hb : phiNormSq φ (fun i => (1 - q i) * a i) ≤ ε := by
    have hstep : ∑ i, star ((1 - q i) * a i) * ((1 - q i) * a i) ≤ 1 - ∑ i, q i * a i := by
      rw [← hb_sum]
      exact Finset.sum_le_sum fun i _ => hb_op i
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => (1 - q i) * a i) hstep
    rw [hval_y] at h
    linarith
  -- The third term `d_i = p_i s - p_i`.
  have hd : phiNormSq φ (fun i => p i * s - p i) ≤ ε := by
    have hsum : ∑ i, (1 - s) * p i * (1 - s) = (1 - s) * (1 - s) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, hpsum, mul_one]
    have hle : (1 - s) * (1 - s) ≤ 1 - ∑ j, q j * a j := by
      have h := one_sub_sq_le_one_sub_sq' hs0 hs1
      rwa [hss] at h
    have hstep : ∑ i, star (p i * s - p i) * (p i * s - p i) ≤ 1 - ∑ j, q j * a j := by
      calc ∑ i, star (p i * s - p i) * (p i * s - p i)
          = ∑ i, (1 - s) * p i * (1 - s) :=
            Finset.sum_congr rfl fun i _ => star_mul_self_proj_mul_sub_self (hp i) hsa
        _ = (1 - s) * (1 - s) := hsum
        _ ≤ 1 - ∑ j, q j * a j := hle
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => p i * s - p i) hstep
    rw [hval_y] at h
    linarith
  -- The second term `c_i = q_i a_i - p_i s`.
  have hc : phiNormSq φ (fun i => q i * a i - p i * s) < ε := by
    have hc_op : ∀ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ a i - a i * a i := by
      intro i
      have hci : q i * a i - p i * s = (s - 1) * (p i * s) := by
        rw [← hsp i]; noncomm_ring
      have hstar_ps : star (p i * s) = s * p i := by
        rw [star_mul, hsa, (hp i).isSelfAdjoint.star_eq]
      have h1 : star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := by
        rw [hci, star_mul_self_sub_one_mul hsa]
      have h2 : star (p i * s) * ((1 - s) * (1 - s)) * (p i * s)
          ≤ star (p i * s) * (1 - s * s) * (p i * s) :=
        conj_le_conj (one_sub_sq_le_one_sub_sq' hs0 hs1) (p i * s)
      have h3 : star (p i * s) * (1 - s * s) * (p i * s) = q i * a i - q i * a i * (q i * a i) := by
        rw [hstar_ps]
        exact conj_one_sub_sq_eq (hp i).isIdempotentElem.eq (hsp i)
      have h4 : q i * a i - q i * a i * (q i * a i) = q i * (a i - a i * a i) :=
        proj_mul_sub_sq (hq i) (hqa i)
      have h5 : q i * (a i - a i * a i) ≤ a i - a i * a i :=
        Orthogonalization.IsStarProjection.mul_le_of_commute (hq i) (sub_nonneg.mpr (haa i))
          ((hqa i).sub_right ((hqa i).mul_right (hqa i)))
      calc star (q i * a i - p i * s) * (q i * a i - p i * s)
          = star (p i * s) * ((1 - s) * (1 - s)) * (p i * s) := h1
        _ ≤ star (p i * s) * (1 - s * s) * (p i * s) := h2
        _ = q i * a i - q i * a i * (q i * a i) := h3
        _ = q i * (a i - a i * a i) := h4
        _ ≤ a i - a i * a i := h5
    have hc_sum : ∑ i, (a i - a i * a i) = 1 - ∑ i, a i * a i := by
      rw [Finset.sum_sub_distrib, ha1]
    have hstep : ∑ i, star (q i * a i - p i * s) * (q i * a i - p i * s) ≤ 1 - ∑ i, a i * a i := by
      rw [← hc_sum]
      exact Finset.sum_le_sum fun i _ => hc_op i
    have h := phiNormSq_le_re_map_of_le (φ := φ) hφ (b := fun i => q i * a i - p i * s) hstep
    rw [hval_aa] at h
    linarith
  -- Assemble: `a_i - p_i = b_i + d_i + c_i` and apply the triangle inequality.
  have hgoal : (φ (∑ i, star (a i - p i) * (a i - p i))).re
      = phiNormSq φ (fun i => a i - p i) := (phiNormSq_eq_re_map_sum _).symm
  rw [hgoal]
  have hfun : (fun i => a i - p i)
      = (fun i => (1 - q i) * a i) + (fun i => p i * s - p i)
        + (fun i => q i * a i - p i * s) := by
    funext i
    simp only [Pi.add_apply]
    noncomm_ring
  rw [hfun]
  exact phiNormSq_add_add_lt hφ hε0 hb hd hc
end Orthogonalization
