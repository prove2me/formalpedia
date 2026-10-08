-- Prove2me | solution 1 for QLLL.PiQSAT.inf_ker_extendOp_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:58:06.463559+00:00
-- url     : https://prove2.me/submissions/b6b46764-dff2-4d4b-b2eb-43ce9bf2f5c4

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_QubitTensor
import Definitions.Def_QLLL_Quantum_KQSAT_PiTensor
import Theorems.Thm_QLLL_PiQSAT_inf_extend_ne_bot
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

/-- Over a field, the kernel of `P ⊗ id_W` is `ker P ⊗ W`.

Write `P` as its injective part after `V → V ⧸ ker P`. Tensoring the injective part with `W`
stays injective because `W` is flat, and right exactness identifies the kernel of the
quotient map tensored with `W`. -/
theorem ker_rTensor_eq_range_mapIncl (P : V →ₗ[K] V') :
    ker (rTensor W P) = range (TensorProduct.mapIncl (ker P) (⊤ : Submodule K W)) := by
  rw [Submodule.tensorProd_top_eq_ker_rTensor_mkQ]
  have hP : P = (ker P).liftQ P le_rfl ∘ₗ (ker P).mkQ := by ext; simp
  have hinj : Function.Injective (rTensor W ((ker P).liftQ P le_rfl)) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (by
      rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl)
  conv_lhs => rw [hP, rTensor_comp]
  exact LinearMap.ker_comp_of_ker_eq_bot _ (LinearMap.ker_eq_bot.mpr hinj)

end LinearMap

end QLLL


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

/-- `ι` qubits span a space of dimension `2 ^ |ι|`. -/
theorem finrank_qubits (ι : Type*) [Fintype ι] :
    finrank ℂ (Qubits ι) = 2 ^ Fintype.card ι := by
  classical
  rw [(localEquiv ι).finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fun,
    Fintype.card_fin]

variable {n : ℕ}

/-- The kernel of `P ⊗ id` is the extension of `ker P`. -/
theorem ker_extendOp (S : Finset (Fin n)) (P : Module.End ℂ (Qubits {i // i ∈ S})) :
    LinearMap.ker (extendOp S P) = extend S (LinearMap.ker P) := by
  rw [extendOp, extend, LinearEquiv.conj_apply, LinearMap.ker_comp, LinearEquiv.ker_comp,
    LinearMap.ker_rTensor_eq_range_mapIncl, Submodule.comap_equiv_eq_map_symm,
    LinearEquiv.symm_symm]

end QLLL.PiQSAT


section

open TensorProduct Module
open QLLL QLLL.QSAT QLLL.QubitTensor
open QLLL
open QLLL.PiQSAT
variable {n : ℕ}

theorem solution {m k r D' : ℕ} (S : Fin m → Finset (Fin n))
    (P : ∀ i, Module.End ℂ (Qubits {j // j ∈ S i}))
    (hcard : ∀ i, (S i).card = k)
    (hrank : ∀ i, finrank ℂ (LinearMap.range (P i)) ≤ r)
    (hdeg : ∀ v : Fin n, (Finset.univ.filter fun i => v ∈ S i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    (⨅ i, LinearMap.ker (extendOp (S i) (P i))) ≠ ⊥ := by
  classical
  simp_rw [ker_extendOp]
  refine inf_extend_ne_bot S (fun i => LinearMap.ker (P i)) hcard (fun i => ?_) hdeg hp
  have hrn := LinearMap.finrank_range_add_finrank_ker (P i)
  rw [finrank_qubits, Fintype.card_coe, hcard i] at hrn
  have h2 : (0 : ℝ) < 2 ^ k := by positivity
  have hr : (finrank ℂ (LinearMap.range (P i)) : ℝ) ≤ r := by exact_mod_cast hrank i
  have hsum : (finrank ℂ (LinearMap.range (P i)) : ℝ) + finrank ℂ (LinearMap.ker (P i))
      = 2 ^ k := by exact_mod_cast hrn
  have h1 : 1 - (r : ℝ) / 2 ^ k = (2 ^ k - r) / 2 ^ k := by field_simp
  rw [h1]
  gcongr
  linarith

end
