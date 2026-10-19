-- Prove2me | solution 1 for Orthogonalization.phiNormSq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:44.646401+00:00
-- url     : https://prove2.me/submissions/c76550af-e1fb-4f6a-937c-26d99e1a6db0

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/PhiNorm.lean (solution of Orthogonalization.phiNormSq_add_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Orthogonalization
section
open scoped ComplexOrder
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
/-- A positive functional takes nonnegative real values on `star x * x`. -/
theorem re_star_mul_self_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x : H →L[ℂ] H) :
    0 ≤ (φ (star x * x)).re :=
  (Complex.nonneg_iff.mp (hφ x)).1
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
/-- **Cauchy–Schwarz inequality** for a positive linear functional, in the form
`|φ (x* y)| ≤ ‖x‖_φ ‖y‖_φ`.

The proof is Mathlib's GNS construction: `φ` becomes a `PositiveLinearMap` and
`x, y ↦ φ (star x * y)` is then the (semi-definite) inner product of
`PositiveLinearMap.PreGNS`, whose Cauchy–Schwarz inequality is
`norm_inner_le_norm`. -/
theorem norm_map_star_mul_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x y : H →L[ℂ] H) :
    ‖φ (star x * y)‖ ≤ Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re) := by
  set f := toPositiveLinearMap φ hφ with hf
  have h := norm_inner_le_norm (𝕜 := ℂ) (f.toPreGNS x) (f.toPreGNS y)
  rw [PositiveLinearMap.preGNS_inner_def, PositiveLinearMap.preGNS_norm_def,
    PositiveLinearMap.preGNS_norm_def] at h
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, hf, toPositiveLinearMap_apply] using h
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ}
/-- The real part of `φ (x* y)` is bounded by `‖x‖_φ ‖y‖_φ`. -/
theorem re_map_star_mul_le (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (x y : H →L[ℂ] H) :
    (φ (star x * y)).re ≤
      Real.sqrt ((φ (star x * x)).re) * Real.sqrt ((φ (star y * y)).re) :=
  le_trans (Complex.re_le_norm _) (norm_map_star_mul_le hφ x y)
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]
/-- The squared seminorm of a tuple is nonnegative. -/
theorem phiNormSq_nonneg (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (b : ι → H →L[ℂ] H) :
    0 ≤ phiNormSq φ b :=
  Finset.sum_nonneg fun i _ => re_star_mul_self_nonneg hφ (b i)
end
end Orthogonalization

namespace Orthogonalization
section
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]
omit [Fintype ι] in
/-- Expansion of the squared seminorm of a sum, coordinatewise. -/
theorem re_map_star_add_mul_add (b c : ι → H →L[ℂ] H) (i : ι) :
    (φ (star ((b + c) i) * (b + c) i)).re
      = (φ (star (b i) * b i)).re + (φ (star (b i) * c i)).re
        + (φ (star (c i) * b i)).re + (φ (star (c i) * c i)).re := by
  have hstar : star ((b + c) i) * (b + c) i
      = star (b i) * b i + star (b i) * c i + star (c i) * b i + star (c i) * c i := by
    simp only [Pi.add_apply, star_add]
    noncomm_ring
  rw [hstar, map_add, map_add, map_add]
  simp
end
end Orthogonalization

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization
open scoped ComplexOrder BigOperators
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {φ : (H →L[ℂ] H) →ₗ[ℂ] ℂ} {ι : Type*} [Fintype ι]
theorem _root_.solution (hφ : ∀ z : H →L[ℂ] H, 0 ≤ φ (star z * z)) (b c : ι → H →L[ℂ] H) :
    Real.sqrt (phiNormSq φ (b + c))
      ≤ Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c) := by
  have hFnn : ∀ i, 0 ≤ (φ (star (b i) * b i)).re := fun i => re_star_mul_self_nonneg hφ (b i)
  have hGnn : ∀ i, 0 ≤ (φ (star (c i) * c i)).re := fun i => re_star_mul_self_nonneg hφ (c i)
  have hBn : 0 ≤ phiNormSq φ b := phiNormSq_nonneg hφ b
  have hCn : 0 ≤ phiNormSq φ c := phiNormSq_nonneg hφ c
  -- Step 1: coordinatewise bound.
  have step1 : ∀ i ∈ (Finset.univ : Finset ι),
      (φ (star ((b + c) i) * (b + c) i)).re
        ≤ (φ (star (b i) * b i)).re
          + 2 * (Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re))
          + (φ (star (c i) * c i)).re := by
    intro i _
    have h1 : (φ (star (b i) * c i)).re
        ≤ Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re) :=
      re_map_star_mul_le hφ (b i) (c i)
    have h2 : (φ (star (c i) * b i)).re
        ≤ Real.sqrt ((φ (star (c i) * c i)).re) * Real.sqrt ((φ (star (b i) * b i)).re) :=
      re_map_star_mul_le hφ (c i) (b i)
    rw [re_map_star_add_mul_add b c i]
    have h2' : (φ (star (c i) * b i)).re
        ≤ Real.sqrt ((φ (star (b i) * b i)).re) * Real.sqrt ((φ (star (c i) * c i)).re) := by
      rw [mul_comm]; exact h2
    linarith
  -- Step 2: sum the coordinatewise bounds.
  have step2 : phiNormSq φ (b + c)
      ≤ phiNormSq φ b
        + 2 * (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                      * Real.sqrt ((φ (star (c i) * c i)).re))
        + phiNormSq φ c := by
    calc phiNormSq φ (b + c) = ∑ i, (φ (star ((b + c) i) * (b + c) i)).re := rfl
      _ ≤ ∑ i, ((φ (star (b i) * b i)).re
            + 2 * (Real.sqrt ((φ (star (b i) * b i)).re)
                    * Real.sqrt ((φ (star (c i) * c i)).re))
            + (φ (star (c i) * c i)).re) := Finset.sum_le_sum step1
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
  -- Step 3: discrete Cauchy–Schwarz on the cross term.
  have step3 : (∑ i, Real.sqrt ((φ (star (b i) * b i)).re)
                        * Real.sqrt ((φ (star (c i) * c i)).re))
      ≤ Real.sqrt (phiNormSq φ b) * Real.sqrt (phiNormSq φ c) :=
    Real.sum_sqrt_mul_sqrt_le Finset.univ hFnn hGnn
  -- Step 4: recognize a perfect square and take square roots.
  have hsq : phiNormSq φ (b + c)
      ≤ (Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c)) ^ 2 := by
    have e1 : Real.sqrt (phiNormSq φ b) ^ 2 = phiNormSq φ b := Real.sq_sqrt hBn
    have e2 : Real.sqrt (phiNormSq φ c) ^ 2 = phiNormSq φ c := Real.sq_sqrt hCn
    nlinarith [step2, step3, e1, e2]
  calc Real.sqrt (phiNormSq φ (b + c))
      ≤ Real.sqrt ((Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (phiNormSq φ b) + Real.sqrt (phiNormSq φ c) :=
        Real.sqrt_sq (by positivity)
end Orthogonalization
