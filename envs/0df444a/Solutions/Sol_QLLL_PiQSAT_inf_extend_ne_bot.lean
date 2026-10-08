-- Prove2me | solution 1 for QLLL.PiQSAT.inf_extend_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:54:21.72249+00:00
-- url     : https://prove2.me/submissions/d7201d2f-f52e-4e83-bea4-9fd7fcda5265

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_QubitTensor
import Definitions.Def_QLLL_Quantum_KQSAT_PiTensor
import Theorems.Thm_QLLL_QSAT_inf_ne_bot_of_degree_le
import Theorems.Thm_QLLL_QSAT_relDim_lift
import Theorems.Thm_QLLL_TensorProduct_range_mapIncl_eq_inf
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

theorem tmul_mem_tensorProd {A : Submodule K V} {B : Submodule K W} {a : V} {b : W}
    (ha : a ∈ A) (hb : b ∈ B) : a ⊗ₜ[K] b ∈ LinearMap.range (TensorProduct.mapIncl A B) :=
  ⟨⟨a, ha⟩ ⊗ₜ[K] ⟨b, hb⟩, rfl⟩

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


-- inline helpers from QuantumLocalLemma.Quantum.KQSAT.Basic
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# k-QSAT and the locality structure

Towards Corollary 16 of arXiv:0911.1696: a `k`-QSAT instance of projectors of
rank at most `r` in which every qubit appears in at most `2 ^ k / (e * r * k)`
projectors is satisfiable.

## Design

The paper works in `⨂ i, H i`. We avoid `PiTensorProduct` entirely by using the
configuration model: the state space of `n` qubits is the space of functions
from bit strings to `ℂ`,
``
H n = (Fin n → Fin 2) → ℂ
``
which is *the same* finite dimensional space, but with locality expressed as an
explicit bipartition of the index type rather than as a tensor factorisation.
Every dimension is then a cardinality.

A constraint supported on a set `S` of qubits is a subspace of the form
`lift S Y`: those `f` all of whose `S`-slices lie in `Y`. This is the
configuration-model description of `Y ⊗ (everything else)`.

## Main results

* `IsSupportedOn.mono` : support is monotone in the set of qubits.
* `finrank_inf_liftL_liftR` : the product rule `dim (U ⊗ W) = dim U * dim W`, in
  the configuration model.
* `relDim_inf_of_isSupportedOn_compl` : a subspace cut out on `S` and one cut out
  on `Sᶜ` are R-independent. This is the crux of the paper's Lemma 11.
* `mutuallyIndepOn_of_isSupportedOn` : Lemma 11, mutual R-independence.
* `inf_ne_bot_of_degree_le`, `inf_lift_ne_bot` : Corollary 16.
-/

namespace QLLL.QSAT

open Finset Module

variable {n : ℕ}

/-! ### Support is monotone

Enlarging the set of qubits. If `S ⊆ T`, a `T`-configuration splits into its
`S`-part and its `T \ S`-part, and a configuration outside `S` splits into its
`T \ S`-part and its part outside `T`. Slicing at `S` therefore factors as
slicing at `T` followed by a relative slice, which is all that is needed. -/

/-! ## The crux, in Kronecker form

Locality in the configuration model is a Kronecker product: reindexing
`Cfg n ≃ CfgIn S × CfgOut S` turns an operator supported on `S` into a matrix of
the form `p ⊗ₖ 1`, and one supported on `Sᶜ` into `1 ⊗ₖ q`. The dimension count
behind the paper's Lemma 11 then reduces to Kronecker algebra, all of which is
already in Mathlib: `Matrix.mul_kronecker_mul`, `Matrix.one_kronecker`,
`Matrix.trace_kronecker`.

This formulation supersedes an earlier one in terms of `Submodule.map₂`. It is
shorter because it needs exactly one fact Mathlib lacks, recorded below, rather
than a theory of product subspaces.

The same modelling convention (configurations, ground spaces as `Submodule`s,
local terms as orthogonal projectors via `Submodule.starProjection`) is used by
TNLean for parent Hamiltonians of matrix product states.
-/

section Crux

open scoped Kronecker

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

end Crux

/-! ## The product rule for an abstract two-factor split

Stated for the concrete product index type `A × B`, so that it can be
instantiated at the splitting `Cfg n ≃ CfgIn S × CfgOut S` in either order.
-/

section Split

open scoped Kronecker

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem colSlice_apply (b : B) (f : (A × B) → ℂ) (a : A) :
    colSlice b f a = f (a, b) := rfl

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem rowSlice_apply (a : A) (f : (A × B) → ℂ) (b : B) :
    rowSlice a f b = f (a, b) := rfl

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
@[simp] theorem liftR_top :
    liftR (⊤ : Submodule ℂ (B → ℂ)) = (⊤ : Submodule ℂ ((A × B) → ℂ)) := by
  simp [liftR]

end Split

/-! ## Transporting the product rule to the qubit splitting -/

section Transport

variable {n : ℕ} {S : Finset (Fin n)}

theorem splitEquiv_apply (g : (CfgIn S × CfgOut S) → ℂ) (c : Cfg n) :
    splitEquiv S g c = g (cfgEquiv S c) := rfl

theorem sliceMap_splitEquiv (b : CfgOut S) (g : (CfgIn S × CfgOut S) → ℂ) :
    sliceMap S b (splitEquiv S g) = colSlice b g := by
  funext a
  simp only [sliceMap, LinearMap.funLeft_apply, splitEquiv_apply, Equiv.apply_symm_apply,
    colSlice_apply]

theorem comap_splitEquiv_lift (Y : Submodule ℂ (HIn S)) :
    Submodule.comap (splitEquiv S : ((CfgIn S × CfgOut S) → ℂ) →ₗ[ℂ] H n) (lift S Y)
      = liftL Y := by
  ext g
  simp only [Submodule.mem_comap, LinearEquiv.coe_coe, lift, liftL, Submodule.mem_iInf,
    Submodule.mem_comap]
  constructor
  · intro h b
    rw [← sliceMap_splitEquiv]
    exact h b
  · intro h b
    rw [sliceMap_splitEquiv]
    exact h b

theorem lift_eq_map_liftL (Y : Submodule ℂ (HIn S)) :
    lift S Y
      = Submodule.map (splitEquiv S : ((CfgIn S × CfgOut S) → ℂ) →ₗ[ℂ] H n) (liftL Y) := by
  rw [← comap_splitEquiv_lift Y,
    Submodule.map_comap_eq_of_surjective (splitEquiv S).surjective]

/-! ### The complementary side

`CfgOut S` and `CfgIn Sᶜ` carry the same data, as do `CfgIn S` and `CfgOut Sᶜ`,
so a subspace supported on `Sᶜ` is a right lift for the splitting at `S`. -/

end Transport

/-! ## Corollary 16: k-QSAT

The combinatorial half is identical to the classical case in `QuantumLocalLemma.Classical.KSAT`:
constraints on `k` qubits each, every qubit touched by at most `D` constraints,
so each constraint overlaps at most `k (D - 1)` others.
-/

theorem card_cfgIn (S : Finset (Fin n)) : Fintype.card (CfgIn S) = 2 ^ S.card := by
  simp [CfgIn]

end QLLL.QSAT


-- inline helpers from QuantumLocalLemma.Quantum.KQSAT.QubitTensor
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# The qubit model, certified against Mathlib's tensor products

`QuantumLocalLemma.Quantum.KQSAT.Basic` models the state space of `n` qubits as
`(Fin n → Fin 2) → ℂ`, functions on bit strings, with locality expressed as
a bipartition of the index type. That is an encoding, not a definition imported
from a library, so on its own it asks the reader to accept that it is the
`n`-qubit space.

This file removes that gap in two steps.

* `qubitsEquiv` : the encoding really is the `n`-fold tensor product,
  `(⨂[ℂ] i : Fin n, (Fin 2 → ℂ)) ≃ₗ[ℂ] ((Fin n → Fin 2) → ℂ)`, with
  `qubitsEquiv_tprod` and `qubitsEquiv_symm_single` pinning down the
  identification on elementary tensors and on computational basis states.

* `funTensorEquiv` and `map_funTensorEquiv_tensorProd` : the two-factor splitting used
  throughout `QuantumLocalLemma.Quantum.KQSAT.Basic` really is the tensor product, and the subspace
  `liftL Y ⊓ liftR W` used there really is `Y ⊗ W`. So the product rule may be
  routed through the standard statement about tensor products of submodules
  (`TensorProduct.range_mapIncl_inf_range_mapIncl`) rather than through the Kronecker computation
  in `QuantumLocalLemma.Quantum.KQSAT.Basic`.

Mathlib has no identification of a `PiTensorProduct` of function spaces with
functions on the product index; the nearest is
`PiTensorProduct.ofFinsuppEquiv'`, stated for `Finsupp`.
-/

open TensorProduct
open QLLL.QSAT

namespace QLLL.QubitTensor

/-! ## The `n`-qubit space is the `n`-fold tensor product -/

/-! ## The two-factor splitting is the tensor product -/

theorem funTensorEquiv_tmul (A B : Type*)
    [Fintype B] [DecidableEq B] (f : A → ℂ) (g : B → ℂ) (a : A) (b : B) :
    funTensorEquiv A B (f ⊗ₜ[ℂ] g) (a, b) = f a * g b := by
  simp [funTensorEquiv, funUncurryEquiv, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul, mul_comm]

section Transport

variable {A B : Type*} [Fintype B] [DecidableEq B]

/-- `Y ⊗ (B → ℂ)` is the set of functions all of whose column slices lie in
`Y`. -/
theorem map_funTensorEquiv_tensorProd_top (Y : Submodule ℂ (A → ℂ)) :
    Submodule.map ((funTensorEquiv A B).toLinearMap)
        (LinearMap.range (TensorProduct.mapIncl Y (⊤ : Submodule ℂ (B → ℂ)))) = liftL Y := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, TensorProduct.range_mapIncl]
    refine Submodule.map₂_le.2 ?_
    intro y hy g _
    simp only [Submodule.mem_comap, TensorProduct.mk_apply, liftL, Submodule.mem_iInf]
    intro b
    have hcol : colSlice b (funTensorEquiv A B (y ⊗ₜ[ℂ] g)) = g b • y := by
      funext a
      simp [colSlice_apply, funTensorEquiv_tmul, mul_comm]
    simp only [LinearEquiv.coe_coe]
    rw [hcol]
    exact Submodule.smul_mem _ _ hy
  · intro f hf
    simp only [liftL, Submodule.mem_iInf, Submodule.mem_comap] at hf
    refine ⟨∑ b : B, (colSlice b f) ⊗ₜ[ℂ] (Pi.single b (1 : ℂ)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun b _ => Submodule.tmul_mem_tensorProd (hf b) Submodule.mem_top
    · funext p
      obtain ⟨a, b⟩ := p
      rw [map_sum, Finset.sum_apply]
      simp [funTensorEquiv_tmul, Pi.single_apply]

/-- `(A → ℂ) ⊗ W` is the set of functions all of whose row slices lie in `W`. -/
theorem map_funTensorEquiv_top_tensorProd [Finite A] (W : Submodule ℂ (B → ℂ)) :
    Submodule.map ((funTensorEquiv A B).toLinearMap)
        (LinearMap.range (TensorProduct.mapIncl (⊤ : Submodule ℂ (A → ℂ)) W)) = liftR W := by
  cases nonempty_fintype A
  classical
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap, TensorProduct.range_mapIncl]
    refine Submodule.map₂_le.2 ?_
    intro g _ w hw
    simp only [Submodule.mem_comap, TensorProduct.mk_apply, liftR, Submodule.mem_iInf]
    intro a
    have hrow : rowSlice a (funTensorEquiv A B (g ⊗ₜ[ℂ] w)) = g a • w := by
      funext b
      simp [rowSlice_apply, funTensorEquiv_tmul]
    simp only [LinearEquiv.coe_coe]
    rw [hrow]
    exact Submodule.smul_mem _ _ hw
  · intro f hf
    simp only [liftR, Submodule.mem_iInf, Submodule.mem_comap] at hf
    refine ⟨∑ a : A, (Pi.single a (1 : ℂ)) ⊗ₜ[ℂ] (rowSlice a f), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun a _ => Submodule.tmul_mem_tensorProd Submodule.mem_top (hf a)
    · funext p
      obtain ⟨a, b⟩ := p
      rw [map_sum, Finset.sum_apply]
      simp [funTensorEquiv_tmul, Pi.single_apply]

end Transport

/-- **The subspace `liftL Y ⊓ liftR W` of `QuantumLocalLemma.Quantum.KQSAT.Basic` is
exactly `Y ⊗ W`.**
This is what ties the configuration model used there to the standard notion of a
tensor product of submodules. -/
theorem map_funTensorEquiv_tensorProd (A B : Type*) [Finite A]
    [Fintype B] [DecidableEq B] (Y : Submodule ℂ (A → ℂ)) (W : Submodule ℂ (B → ℂ)) :
    Submodule.map (funTensorEquiv A B : _ →ₗ[ℂ] _)
        (LinearMap.range (TensorProduct.mapIncl Y W))
      = QLLL.QSAT.liftL Y ⊓ QLLL.QSAT.liftR W := by
  rw [TensorProduct.range_mapIncl_eq_inf, Submodule.map_inf _ (funTensorEquiv A B).injective,
    map_funTensorEquiv_tensorProd_top, map_funTensorEquiv_top_tensorProd]

/-! ## The product rule, via the standard statement

With the identification in place, the dimension count behind the paper's
Lemma 11 follows from `TensorProduct.range_mapIncl_inf_range_mapIncl` and
`Module.finrank_tensorProduct`, with no Kronecker products and no trace
computation. `QLLL.QSAT.finrank_inf_liftL_liftR` proves the same thing the other
way; having both is a cross-check on the model.
-/

/-! ## The identification is isometric

Mathlib does put the Hilbert inner product on the *algebraic* tensor product
(`TensorProduct.instInnerProductSpace`), and `OrthonormalBasis.tensorProduct`
builds the product orthonormal basis, so for two factors the identification is
isometric essentially for free. That matters because it is what carries
"orthogonal projector" and "orthogonal complement" across the identification,
which a purely linear isomorphism would not.

`euclideanTensorIsometry_eq_funTensorEquiv` shows the isometry is the *same
underlying map* as `funTensorEquiv` above, read through `WithLp.linearEquiv`. So
the configuration model is not merely linearly isomorphic to the tensor product;
it is the isometric identification, up to the `WithLp` type synonym.

Two limits are worth recording. Mathlib puts no inner product on
`PiTensorProduct`, and `⨂[𝕜] i, E i` already carries a `SeminormedAddCommGroup`
from `PiTensorProduct.projectiveSeminorm`, the projective tensor norm rather than
the Hilbert one, so the `n`-fold Hilbert structure cannot be added as an instance
on that type at all. What is stated here instead is
`inner_qubitsEuclidEquiv_tprod`, the defining property
`⟪⊗ᵢ fᵢ, ⊗ᵢ gᵢ⟫ = ∏ᵢ ⟪fᵢ, gᵢ⟫`, which needs no new instance.

Also, `WithLp` is a structure, so `EuclideanSpace ℂ A` is not definitionally
`A → ℂ`, and there is deliberately no isometry between them for `p = 2` (the bare
function type carries the sup norm). Making the state space of
`QuantumLocalLemma.Quantum.KQSAT.Basic`
carry an inner product would therefore be a change of type, not an addition of
lemmas. It is not done here because nothing in the local lemma needs it: the
physical projectors of `QuantumLocalLemma.Quantum.KQSAT.Projector` already obtain self-adjointness
by
transporting to `EuclideanSpace` locally.
-/

section Isometric

open scoped ComplexOrder

variable {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-! ### The `n`-fold case, without new instances -/

end Isometric

end QLLL.QubitTensor


-- inline helpers from QuantumLocalLemma.Quantum.KQSAT.PiTensor
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Corollary 16 on Mathlib's tensor product

Elsewhere in the project the `n`-qubit space is the configuration model
`(Fin n → Fin 2) → ℂ`. This file states the `k`-QSAT corollary directly on Mathlib's
tensor power `⨂[ℂ] i : Fin n, (Fin 2 → ℂ)`, so that its hypotheses and conclusion use only
Mathlib's definitions.

A constraint on the qubits in `S` lives on `⨂[ℂ] i : S, (Fin 2 → ℂ)`. It is extended to all
qubits through the splitting `(⨂ S) ⊗ (⨂ Sᶜ) ≃ ⨂ (Fin n)` built from Mathlib's
`PiTensorProduct.tmulEquiv` and `PiTensorProduct.reindex`: a subspace `Y` becomes `Y ⊗ ⊤`,
and an operator `P` becomes `P ⊗ id`. The results are transported from the configuration
model, where `map_extend` identifies extension with `QSAT.lift`.

## Main results

* `QLLL.PiQSAT.inf_extend_ne_bot` : Corollary 16 for subspaces.
* `QLLL.PiQSAT.inf_ker_extendOp_ne_bot` : Corollary 16 for local operators of rank at
  most `r`: the extended operators have a common nonzero vector in their kernels.
-/

open TensorProduct Module
open QLLL QLLL.QSAT QLLL.QubitTensor

namespace QLLL.PiQSAT

theorem localEquiv_tprod {ι : Type*} [Fintype ι] (f : ι → Q)
    (c : ι → Fin 2) :
    localEquiv ι (PiTensorProduct.tprod ℂ f) c = ∏ i, f i (c i) := by
  simp [localEquiv, Module.Basis.equivFun_apply, Basis.piTensorProduct_repr_tprod_apply]

variable {n : ℕ}

/-- The splitting, read in the configuration model, is `splitEquiv ∘ funTensorEquiv`. -/
theorem localEquiv_comp_split (S : Finset (Fin n)) :
    (localEquiv (Fin n)).toLinearMap ∘ₗ (split S).toLinearMap =
      (splitEquiv S).toLinearMap ∘ₗ (funTensorEquiv (CfgIn S) (CfgOut S)).toLinearMap ∘ₗ
        TensorProduct.map (localEquiv {i // i ∈ S}).toLinearMap
          (localEquiv {i // i ∉ S}).toLinearMap := by
  classical
  have key : ∀ (f : {i // i ∈ S} → Q) (g : {i // i ∉ S} → Q),
      localEquiv (Fin n) (split S (PiTensorProduct.tprod ℂ f ⊗ₜ PiTensorProduct.tprod ℂ g)) =
        splitEquiv S (funTensorEquiv (CfgIn S) (CfgOut S)
          (localEquiv _ (PiTensorProduct.tprod ℂ f) ⊗ₜ
            localEquiv _ (PiTensorProduct.tprod ℂ g))) := by
    intro f g
    funext c
    rw [splitEquiv_apply]
    have hc : cfgEquiv S c = (fun i => c i.1, fun i => c i.1) := rfl
    simp only [split, LinearEquiv.trans_apply, PiTensorProduct.tmulEquiv_apply,
      PiTensorProduct.reindex_tprod, localEquiv_tprod, hc, funTensorEquiv_tmul]
    rw [← (Equiv.sumCompl (· ∈ S)).prod_comp, Fintype.prod_sum_type]
    simp
  refine TensorProduct.ext' fun x y => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r' g =>
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        TensorProduct.map_tmul, map_smul, TensorProduct.smul_tmul_smul]
      rw [key]
    | add y₁ y₂ h₁ h₂ => simp_all [TensorProduct.tmul_add]
  | add x₁ x₂ h₁ h₂ => simp_all [TensorProduct.add_tmul]

/-- The image of `A ⊗ B` under `f ⊗ g` is `f(A) ⊗ g(B)`. -/
theorem map_range_mapIncl {V W V' W' : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W']
    [Module ℂ W'] (f : V →ₗ[ℂ] V') (g : W →ₗ[ℂ] W') (A : Submodule ℂ V)
    (B : Submodule ℂ W) :
    (LinearMap.range (TensorProduct.mapIncl A B)).map (TensorProduct.map f g) =
      LinearMap.range (TensorProduct.mapIncl (A.map f) (B.map g)) := by
  simp only [TensorProduct.range_mapIncl, Submodule.map_map₂, Submodule.map₂_map_map]
  congr 1

/-- **The bridge.** Extension by `⊗ ⊤` in the tensor model is `QSAT.lift` in the
configuration model. -/
theorem map_extend (S : Finset (Fin n)) (Y : Submodule ℂ (Qubits {i // i ∈ S})) :
    (extend S Y).map (localEquiv (Fin n)).toLinearMap =
      QSAT.lift S (Y.map (localEquiv {i // i ∈ S}).toLinearMap) := by
  classical
  rw [extend, ← Submodule.map_comp, localEquiv_comp_split, Submodule.map_comp,
    Submodule.map_comp, map_range_mapIncl, Submodule.map_top, LinearEquiv.range,
    map_funTensorEquiv_tensorProd, liftR_top, inf_top_eq, lift_eq_map_liftL]

end QLLL.PiQSAT


section

open TensorProduct Module
open QLLL QLLL.QSAT QLLL.QubitTensor
open QLLL
open QLLL.PiQSAT
variable {n : ℕ}

theorem solution {m k D' : ℕ} {p : ℝ} (S : Fin m → Finset (Fin n))
    (Y : ∀ i, Submodule ℂ (Qubits {j // j ∈ S i}))
    (hcard : ∀ i, (S i).card = k)
    (hY : ∀ i, 1 - p ≤ (finrank ℂ (Y i) : ℝ) / 2 ^ k)
    (hdeg : ∀ v : Fin n, (Finset.univ.filter fun i => v ∈ S i).card ≤ D' + 1)
    (hp : p * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    (⨅ i, extend (S i) (Y i)) ≠ ⊥ := by
  classical
  have key := QSAT.inf_ne_bot_of_degree_le (Sq := S)
    (X := fun i => QSAT.lift (S i) ((Y i).map (localEquiv {j // j ∈ S i}).toLinearMap))
    (fun i => ⟨_, rfl⟩) hcard (p := p) (fun i => by
      rw [relDim_lift, card_cfgIn, hcard i, LinearEquiv.finrank_map_eq]
      simpa using hY i) hdeg hp
  intro h
  apply key
  rw [Finset.inf_univ_eq_iInf]
  simp_rw [← map_extend, Submodule.map_equiv_eq_comap_symm, ← Submodule.comap_iInf, h,
    Submodule.comap_bot, LinearEquiv.ker]

end
