-- Prove2me | solution 1 for Orthogonalization.FinDim.exists_isometryData
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:16:57.439606+00:00
-- url     : https://prove2.me/submissions/a8b48352-09c8-4e1b-9abc-51029943f76c

/-
Copyright (c) 2026 the commuting-repetition contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE. Vendored from
https://github.com/vidick/commuting-repetition (commit 8ff85e29, 2026-09-10) by scripts/vendor-repetition.py;
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Completion.lean
-/
/-
# Step F2 in finite dimension: producing the isometry data

From projections `q i` commuting with the POVM elements `a i` and with
`∑ tr(q i) = dim H` (the output of Lemma 3.1), build the block-wise partial
isometry `w` of `IsometryData` (the paper's `u` of Lemma 3.2 read block by
block): `T := ∑ embed i ∘ q i √a i : H → H^ι` satisfies `T* T = y = (√y)²`
with `y = ∑ q i a i`, its range lies in the range of the block projection
`Q = ∑ embed i ∘ q i ∘ proj i`, whose dimension is `∑ tr(q i) = dim H`; the
isometric completion `u` of `T` then gives `w i := proj i ∘ u`. Proof-side.
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
do not edit by hand. Upstream path: orthogonalization/Orthogonalization/FinDim/Blocks.lean
-/
/-
# The block space `H^ι` and its coordinate maps

`BlockSpace H ι := PiLp 2 (fun _ : ι => H)` is the Hilbert space direct sum of
`card ι` copies of `H`; `embed i : H → H^ι` and `proj i : H^ι → H` are the
coordinate maps, adjoint to each other, with `proj i ∘ embed j = δᵢⱼ` and
`∑ embed i ∘ proj i = 1`. This is the paper's `M_n(M)` picture read on
vectors (cf. the sister project's `VN/BlockOperators`, which is specific to
its tracial standard forms). Proof-side.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Completion.lean (solution of Orthogonalization.FinDim.exists_isometryData);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Notation.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Module.PositiveLinearMap
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Int.Defs
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
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.CStarAlgebra.Module.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
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
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Submodule
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.FunLike.Basic
import Mathlib.Data.FunLike.Equiv
import Mathlib.Data.FunLike.IsApply
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.NNReal.Star
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Operations
import Mathlib.Data.SetLike.Basic
import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Notation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Result
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Algebra.Star.Real
import Mathlib.Topology.Algebra.UniformMulAction
import Mathlib.Topology.Constructions
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.UniformSpace.Defs
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_Positivity
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_IsometryData
import Definitions.Def_MIPRE_Background_Orthonormalization_Orthogonalization_FinDim_Blocks
import Theorems.Thm_Orthogonalization_FinDim_exists_isometry_completion
import Theorems.Thm_Orthogonalization_FinDim_trace_blockProj

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
/-- Anything commuting with `y` commutes with `√y`: the square root is a
continuous functional calculus of `y`. (Positivity of `y` is not needed
because of the junk value.) -/
theorem Commute.sqrt (h : Commute x y) : Commute x (CFC.sqrt y) :=
  (Commute.cfcₙ_nnreal h.symm NNReal.sqrt).symm
end
end Orthogonalization

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Evaluating a finite sum of block vectors coordinatewise. -/
theorem sumA {κ : Type*} (s : Finset κ) (f : κ → BlockSpace H ι) (j : ι) :
    (∑ k ∈ s, f k) j = ∑ k ∈ s, f k j := by
  show WithLp.ofLp (∑ k ∈ s, f k) j = ∑ k ∈ s, WithLp.ofLp (f k) j
  rw [WithLp.ofLp_sum, Finset.sum_apply]
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Applying a finite sum of operators. -/
theorem sumCLM {κ : Type*} {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (s : Finset κ) (f : κ → E →L[ℂ] F) (v : E) :
    (∑ k ∈ s, f k) v = ∑ k ∈ s, f k v := by
  rw [ContinuousLinearMap.coe_sum', Finset.sum_apply]
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem embed_apply (i j : ι) (v : H) : embed i v j = if j = i then v else 0 := by
  unfold embed
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, PiLp.coe_symm_continuousLinearEquiv]
  show (ContinuousLinearMap.pi fun j : ι =>
      if j = i then ContinuousLinearMap.id ℂ H else 0) v j = _
  rw [ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem proj_apply (i : ι) (w : BlockSpace H ι) : proj i w = w i := rfl
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem sum_embed_proj_apply (w : BlockSpace H ι) : ∑ i, embed i (proj i w) = w := by
  ext j
  rw [sumA]
  simp only [embed_apply, proj_apply]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem inner_embed_left (i : ι) (v : H) (w : BlockSpace H ι) :
    ⟪embed i v, w⟫_ℂ = ⟪v, w i⟫_ℂ := by
  simp only [PiLp.inner_apply, embed_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (Finset.mem_univ i) h
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem adjoint_embed (i : ι) : adjoint (embed (H := H) i) = proj (ι := ι) i := by
  symm
  rw [eq_adjoint_iff]
  intro w v
  rw [proj_apply]
  conv_rhs => rw [← inner_conj_symm, inner_embed_left, inner_conj_symm]
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem adjoint_proj (i : ι) : adjoint (proj (H := H) (ι := ι) i) = embed i := by
  rw [← adjoint_embed, adjoint_adjoint]
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem blockMap_apply (X : ι → H →L[ℂ] H) (v : H) : blockMap X v = ∑ i, embed i (X i v) := by
  rw [blockMap, sumCLM]; rfl
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem proj_blockMap_apply (X : ι → H →L[ℂ] H) (i : ι) (v : H) :
    proj i (blockMap X v) = X i v := by
  rw [blockMap_apply, proj_apply, sumA]
  simp only [embed_apply]
  rw [Finset.sum_ite_eq Finset.univ i]
  simp
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem proj_comp_blockMap (X : ι → H →L[ℂ] H) (i : ι) : proj i ∘L blockMap X = X i := by
  ext v
  exact proj_blockMap_apply X i v
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem blockProj_apply (q : ι → H →L[ℂ] H) (w : BlockSpace H ι) :
    blockProj q w = ∑ i, embed i (q i (w i)) := by
  rw [blockProj, sumCLM]; rfl
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem blockProj_apply_coord (q : ι → H →L[ℂ] H) (w : BlockSpace H ι) (j : ι) :
    blockProj q w j = q j (w j) := by
  rw [blockProj_apply, sumA]
  simp only [embed_apply]
  rw [Finset.sum_ite_eq Finset.univ j]
  simp
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem proj_blockProj_embed (q : ι → H →L[ℂ] H) (i j : ι) (v : H) :
    proj i (blockProj q (embed j v)) = if i = j then q i v else 0 := by
  rw [proj_apply, blockProj_apply_coord, embed_apply]
  split_ifs with h
  · subst h; rfl
  · simp
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem blockProj_blockMap (q X : ι → H →L[ℂ] H) (v : H) :
    blockProj q (blockMap X v) = blockMap (fun i => q i ∘L X i) v := by
  ext j
  rw [blockProj_apply_coord]
  show q j (proj j (blockMap X v)) = proj j (blockMap (fun i => q i ∘L X i) v)
  rw [proj_blockMap_apply, proj_blockMap_apply]
  rfl
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Module Orthogonalization
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem blockProj_isStarProjection (q : ι → H →L[ℂ] H) (hq : ∀ i, IsStarProjection (q i)) :
    IsStarProjection (blockProj q) := by
  refine ⟨?_, ?_⟩
  · show blockProj q ∘L blockProj q = blockProj q
    ext w j
    show (blockProj q (blockProj q w)) j = (blockProj q w) j
    rw [blockProj_apply_coord, blockProj_apply_coord, ← ContinuousLinearMap.mul_apply, (hq j).isIdempotentElem.eq]
  · rw [IsSelfAdjoint, star_eq_adjoint]
    symm
    rw [eq_adjoint_iff]
    intro w w'
    simp only [PiLp.inner_apply, blockProj_apply_coord]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← adjoint_inner_left, ← star_eq_adjoint, (hq j).isSelfAdjoint.star_eq]
end
end Orthogonalization.FinDim

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Orthogonalization.FinDim
open scoped InnerProductSpace ComplexOrder
open ContinuousLinearMap Module Orthogonalization
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem _root_.solution (a q : ι → H →L[ℂ] H) (ha0 : ∀ i, 0 ≤ a i)
    (hq : ∀ i, IsStarProjection (q i)) (hqa : ∀ i, Commute (q i) (a i))
    (htr : ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) = (finrank ℂ H : ℂ)) :
    ∃ w : ι → H →L[ℂ] H, IsometryData a q w := by
  classical
  -- square roots of the `a i` and of `y = ∑ q i a i`
  set r : ι → H →L[ℂ] H := fun i => CFC.sqrt (a i) with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => CFC.sqrt_nonneg (a i)
  have hrsa : ∀ i, star (r i) = r i := fun i => (IsSelfAdjoint.of_nonneg (hr0 i)).star_eq
  have hrr : ∀ i, r i * r i = a i := fun i => CFC.sqrt_mul_sqrt_self (a i) (ha0 i)
  have hqr : ∀ i, Commute (q i) (r i) := fun i => Orthogonalization.Commute.sqrt (hqa i)
  have hqsa : ∀ i, star (q i) = q i := fun i => (hq i).isSelfAdjoint.star_eq
  have hqq : ∀ i, q i * q i = q i := fun i => (hq i).isIdempotentElem.eq
  set y : H →L[ℂ] H := ∑ i, q i * a i with hy
  have hy0 : 0 ≤ y :=
    Finset.sum_nonneg fun i _ => mul_nonneg_of_commute (hq i).nonneg (ha0 i) (hqa i)
  set s : H →L[ℂ] H := CFC.sqrt y with hs_def
  have hs0 : 0 ≤ s := CFC.sqrt_nonneg y
  have hss : s * s = y := CFC.sqrt_mul_sqrt_self y hy0
  have hs : IsSelfAdjoint s := IsSelfAdjoint.of_nonneg hs0
  -- the block map `T` and `T* T = s²`
  set T : H →L[ℂ] BlockSpace H ι := blockMap (fun i => q i * r i) with hT_def
  have hT : adjoint T ∘L T = s ∘L s := by
    ext v
    rw [comp_apply, comp_apply, ← ContinuousLinearMap.mul_apply, hss, hy, sumCLM]
    -- `T* (T v) = ∑ i, (q i r i)* (q i r i) v`
    have h1 : adjoint T (T v) = ∑ i, adjoint (q i * r i) (proj i (T v)) := by
      have : adjoint T = ∑ i, adjoint (q i * r i) ∘L proj i := by
        simp only [T, blockMap, map_sum, adjoint_comp, adjoint_embed]
      rw [this, sumCLM]
      rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT_def, proj_blockMap_apply, ← comp_apply, ← star_eq_adjoint]
    show (star (q i * r i) * (q i * r i)) v = (q i * a i) v
    congr 1
    rw [star_mul, hrsa, hqsa, mul_assoc, ← mul_assoc (q i), hqq, ← mul_assoc, ← (hqr i).eq,
      mul_assoc, hrr]
  -- the block projection `Q`, its range `L` and `dim L = dim H`
  set Q := blockProj q with hQ_def
  have hQproj := blockProj_isStarProjection q hq
  set L : Submodule ℂ (BlockSpace H ι) := LinearMap.range (Q : BlockSpace H ι →ₗ[ℂ] _) with hL_def
  have hTL : LinearMap.range (T : H →ₗ[ℂ] BlockSpace H ι) ≤ L := by
    rintro _ ⟨v, rfl⟩
    refine ⟨T v, ?_⟩
    show Q (T v) = T v
    rw [hQ_def, hT_def, blockProj_blockMap]
    have hfun : (fun i => q i ∘L (q i * r i)) = fun i => q i * r i := by
      funext i
      rw [← mul_def, ← mul_assoc, hqq]
    rw [hfun]
  have hL : finrank ℂ L = finrank ℂ H := by
    have hproj : LinearMap.IsProj L (Q : BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) :=
      ⟨fun x => ⟨x, rfl⟩, by
        rintro _ ⟨x, rfl⟩
        show Q (Q x) = Q x
        rw [← ContinuousLinearMap.mul_apply, hQproj.isIdempotentElem.eq]⟩
    have htrQ := hproj.trace
    rw [hQ_def, trace_blockProj, htr] at htrQ
    exact_mod_cast htrQ.symm
  -- the isometric completion and its blocks
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_isometry_completion T s hs hs0 hT L hTL hL
  have hQL : L.starProjection = Q := by
    obtain ⟨_, hQ'⟩ := isStarProjection_iff_eq_starProjection_range.mp hQproj
    exact hQ'.symm
  refine ⟨fun i => proj i ∘L u, ?_, ?_, ?_⟩
  · -- (W1)
    ext v
    rw [sumCLM]
    have : ∀ i, (star (proj i ∘L u) * (proj i ∘L u)) v = adjoint u (embed i (proj i (u v))) := by
      intro i
      rw [ContinuousLinearMap.mul_apply, star_eq_adjoint, adjoint_comp, adjoint_proj, comp_apply,
        comp_apply]
    simp only [this]
    rw [← map_sum, sum_embed_proj_apply, ← comp_apply, hu1, one_apply_eq_self]
  · -- (W2)
    intro i j
    ext v
    rw [ContinuousLinearMap.mul_apply, star_eq_adjoint, adjoint_comp, adjoint_proj, comp_apply,
      comp_apply, ← comp_apply u, hu2, hQL, hQ_def, proj_blockProj_embed]
    split_ifs <;> simp
  · -- (W3)
    intro i
    rw [mul_def, comp_assoc, hu3, hT_def, proj_comp_blockMap]
end Orthogonalization.FinDim
