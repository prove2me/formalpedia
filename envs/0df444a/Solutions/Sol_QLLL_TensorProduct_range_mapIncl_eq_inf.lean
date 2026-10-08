-- Prove2me | solution 1 for QLLL.TensorProduct.range_mapIncl_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:11.031922+00:00
-- url     : https://prove2.me/submissions/0219f9e4-4821-4b13-a3d4-7ee49f990662

import Mathlib

-- inline helpers from QuantumLocalLemma.ForMathlib.LinearAlgebra.TensorProduct.Submodule
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Intersections of tensor products of subspaces

For subspaces `A, A' ≤ V` and `B, B' ≤ W` of vector spaces over a field `K`,

  `(A ⊗ B) ⊓ (A' ⊗ B') = (A ⊓ A') ⊗ (B ⊓ B')`

inside `V ⊗[K] W`. Mathlib has `Submodule.map₂_sup_left` and
`Submodule.map₂_sup_right`, which hold for an arbitrary bilinear map, but no `inf`
counterpart. The `inf` statement is genuinely less formal: it fails for general
bilinear maps, and for tensor products it uses flatness, supplied here by working
over a field.

The results are written in Mathlib's vocabulary and are candidates for upstreaming,
which is why they live under `ForMathlib` and in Mathlib's namespaces.

## Notation

The subspace `A ⊗ B` of `V ⊗[K] W` is Mathlib's `LinearMap.range (TensorProduct.mapIncl A B)`,
the range of `A ⊗[K] B → V ⊗[K] W`; `TensorProduct.range_mapIncl` identifies it with
`Submodule.map₂ (TensorProduct.mk K V W) A B`. No new definition is introduced.

## Main results

* `LinearMap.exists_comp_add_comp` : over a field, a linear map vanishing on
  `ker f ⊓ ker g` factors as `u ∘ f + v ∘ g`.
* `TensorProduct.range_mapIncl_eq_inf` : `A ⊗ B = (A ⊗ W) ⊓ (V ⊗ B)`.
* `TensorProduct.range_mapIncl_inf_range_mapIncl` : the intersection formula above.
* `Submodule.map₂_mk_inf_map₂_mk` : the same formula in the `Submodule.map₂` form.
* `Submodule.finrank_tensorProd` : `dim (A ⊗ B) = dim A * dim B`.
* `Submodule.finrank_tensorProd_sup_tensorProd` : inclusion-exclusion for
  `(A₁ ⊗ B₁) ⊔ (A₂ ⊗ B₂)`.

## Applications

In this project the intersection formula is the product rule behind Lemma 11 of
Ambainis-Kempe-Sattath (see `QuantumLocalLemma.Quantum.KQSAT.QubitTensor`). The
inclusion-exclusion formula is also the deterministic core of an exact quantum
max-flow computation for the three-vertex network of Cui-Freedman-Sattath-Stong-Minton
(arXiv:1508.04644): with a GHZ tensor at the centre, the image of the network map is
`(A₁ ⊗ B₁) + (A₂ ⊗ B₂)`.
-/

open TensorProduct LinearMap Function

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

namespace QLLL
open TensorProduct
open LinearMap

namespace LinearMap
open _root_.LinearMap

/-! ## A factorisation lemma over a field -/

section Factor

variable {M N H : Type*}
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  [AddCommGroup H] [Module K H]

end Factor

end LinearMap

namespace Submodule
open _root_.Submodule

/-! ## Tensor products of subspaces -/

theorem tensorProd_mono {A A' : Submodule K V} {B B' : Submodule K W}
    (hA : A ≤ A') (hB : B ≤ B') :
    LinearMap.range (TensorProduct.mapIncl A B)
      ≤ LinearMap.range (TensorProduct.mapIncl A' B') := by
  rw [TensorProduct.range_mapIncl, TensorProduct.range_mapIncl]
  exact Submodule.map₂_le_map₂ hA hB

/-- `A ⊗ W` is exactly the kernel of `V ⊗ W → (V ⧸ A) ⊗ W`.

This is right exactness of the tensor product, so no flatness is needed. -/
theorem tensorProd_top_eq_ker_rTensor_mkQ (A : Submodule K V) :
    LinearMap.range (TensorProduct.mapIncl A (⊤ : Submodule K W)) = ker (rTensor W A.mkQ) := by
  have hex : Function.Exact A.subtype A.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  have hsurj : Function.Surjective A.mkQ := Submodule.mkQ_surjective A
  have hE : Function.Exact (rTensor W A.subtype) (rTensor W A.mkQ) :=
    _root_.rTensor_exact W hex hsurj
  rw [LinearMap.exact_iff] at hE
  rw [hE, TensorProduct.range_mapIncl, LinearMap.rTensor_def, TensorProduct.range_map,
    Submodule.range_subtype, LinearMap.range_id]

/-- The symmetric statement: `V ⊗ B` is the kernel of `V ⊗ W → V ⊗ (W ⧸ B)`. -/
theorem top_tensorProd_eq_ker_lTensor_mkQ (B : Submodule K W) :
    LinearMap.range (TensorProduct.mapIncl (⊤ : Submodule K V) B) = ker (lTensor V B.mkQ) := by
  have hex : Function.Exact B.subtype B.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  have hsurj : Function.Surjective B.mkQ := Submodule.mkQ_surjective B
  have hE : Function.Exact (lTensor V B.subtype) (lTensor V B.mkQ) :=
    _root_.lTensor_exact V hex hsurj
  rw [LinearMap.exact_iff] at hE
  rw [hE, TensorProduct.range_mapIncl, LinearMap.lTensor_def, TensorProduct.range_map,
    Submodule.range_subtype, LinearMap.range_id]

end Submodule

namespace TensorProduct
open _root_.TensorProduct

end TensorProduct

namespace Submodule
open _root_.Submodule

/-! ## The same statement with `Submodule.map₂` -/

end Submodule

/-! ## The rank identity behind the closed form

With a GHZ tensor at the centre of the three-vertex network, the image of the
network map is `(A₁ ⊗ B₁) + (A₂ ⊗ B₂)`, so its dimension is pinned by
inclusion-exclusion together with `TensorProduct.range_mapIncl_inf_range_mapIncl`.
This is the deterministic
core of `QMF = 2αβ − α′β′`; the genericity half (that the relevant subspace
dimensions take their generic values) is not formalised here.
-/

namespace Submodule
open _root_.Submodule

open Module

variable [FiniteDimensional K V] [FiniteDimensional K W]

end Submodule

namespace LinearMap
open _root_.LinearMap

/-! ## Kernels of operators tensored with the identity -/

variable {V' : Type*} [AddCommGroup V'] [Module K V']

end LinearMap

end QLLL


section

open TensorProduct LinearMap Function
variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
open QLLL
open _root_.TensorProduct

theorem solution (A : Submodule K V) (B : Submodule K W) :
    LinearMap.range (TensorProduct.mapIncl A B)
      = LinearMap.range (TensorProduct.mapIncl A (⊤ : Submodule K W))
        ⊓ LinearMap.range (TensorProduct.mapIncl (⊤ : Submodule K V) B) := by
  refine le_antisymm (le_inf (Submodule.tensorProd_mono le_rfl le_top)
    (Submodule.tensorProd_mono le_top le_rfl)) ?_
  rintro x ⟨hx1, hx2⟩
  rw [Submodule.tensorProd_top_eq_ker_rTensor_mkQ] at hx1
  rw [Submodule.top_tensorProd_eq_ker_lTensor_mkQ] at hx2
  -- `x` comes from `A ⊗ W`.
  have hexA : Function.Exact A.subtype A.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  have hEA := _root_.rTensor_exact (Q := W) hexA (Submodule.mkQ_surjective A)
  rw [LinearMap.exact_iff] at hEA
  rw [hEA] at hx1
  obtain ⟨y, rfl⟩ := hx1
  -- Its image in `A ⊗ (W ⧸ B)` vanishes, because `A ↪ V` stays injective after
  -- tensoring with the flat module `W ⧸ B`.
  have hcomp : lTensor V B.mkQ (rTensor W A.subtype y)
      = rTensor (W ⧸ B) A.subtype (lTensor (A : Type _) B.mkQ y) := by
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
      LinearMap.lTensor_comp_rTensor, LinearMap.rTensor_comp_lTensor]
  simp only [SetLike.mem_coe, LinearMap.mem_ker] at hx2
  rw [hcomp] at hx2
  have hinj : Function.Injective (rTensor (W ⧸ B) A.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype A)
  have hy : lTensor (A : Type _) B.mkQ y = 0 := by
    apply hinj; rw [hx2, map_zero]
  -- Hence `y` comes from `A ⊗ B`.
  have hexB : Function.Exact B.subtype B.mkQ := by
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_subtype]
  have hEB := _root_.lTensor_exact (Q := (A : Type _)) hexB (Submodule.mkQ_surjective B)
  rw [LinearMap.exact_iff] at hEB
  have hy' : y ∈ range (lTensor (A : Type _) B.subtype) := by
    rw [← hEB]; exact LinearMap.mem_ker.mpr hy
  obtain ⟨z, rfl⟩ := hy'
  have hz : rTensor W A.subtype (lTensor (A : Type _) B.subtype z)
      = TensorProduct.mapIncl A B z := by
    rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
  rw [hz]
  exact ⟨z, rfl⟩

end
