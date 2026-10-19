-- Prove2me | solution 1 for Orthogonalization.FinDim.trace_blockProj
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:14:38.767741+00:00
-- url     : https://prove2.me/submissions/3c94b19d-0676-4e04-b001-002de127bc59

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/Orthonormalization/Orthogonalization/FinDim/Completion.lean (solution of Orthogonalization.FinDim.trace_blockProj);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem proj_embed (i j : ι) (v : H) : proj i (embed j v) = if i = j then v else 0 := by
  rw [proj_apply, embed_apply]
end
end Orthogonalization.FinDim

namespace Orthogonalization.FinDim
section
open scoped InnerProductSpace
open ContinuousLinearMap
set_option autoImplicit true
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem proj_embed_same (i : ι) (v : H) : proj i (embed i v) = v := by simp [proj_embed]
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
theorem _root_.solution (q : ι → H →L[ℂ] H) :
    LinearMap.trace ℂ (BlockSpace H ι) (blockProj q : BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) =
      ∑ i, LinearMap.trace ℂ H (q i : H →ₗ[ℂ] H) := by
  have hcoe : ((blockProj q : BlockSpace H ι →L[ℂ] BlockSpace H ι) :
      BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) =
      ∑ i, ((embed i ∘L q i ∘L proj i : BlockSpace H ι →L[ℂ] BlockSpace H ι) :
        BlockSpace H ι →ₗ[ℂ] BlockSpace H ι) := by
    refine LinearMap.ext fun v => ?_
    rw [LinearMap.sum_apply]
    simp only [ContinuousLinearMap.coe_coe]
    rw [blockProj, sumCLM]
  rw [hcoe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show LinearMap.trace ℂ (BlockSpace H ι)
      (((embed i : H →L[ℂ] BlockSpace H ι) : H →ₗ[ℂ] BlockSpace H ι) ∘ₗ
        (((q i : H →L[ℂ] H) : H →ₗ[ℂ] H) ∘ₗ
          ((proj i : BlockSpace H ι →L[ℂ] H) : BlockSpace H ι →ₗ[ℂ] H))) = _
  rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
  have : ((proj i : BlockSpace H ι →L[ℂ] H) : BlockSpace H ι →ₗ[ℂ] H) ∘ₗ
      ((embed i : H →L[ℂ] BlockSpace H ι) : H →ₗ[ℂ] BlockSpace H ι) = LinearMap.id := by
    ext v
    exact proj_embed_same i v
  rw [this, LinearMap.comp_id]
end Orthogonalization.FinDim
