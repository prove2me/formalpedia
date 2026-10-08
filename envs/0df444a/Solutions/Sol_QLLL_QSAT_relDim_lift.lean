-- Prove2me | solution 1 for QLLL.QSAT.relDim_lift
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:51:39.619552+00:00
-- url     : https://prove2.me/submissions/8c8431df-93e0-48e7-a1d6-a58dc9029392

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Theorems.Thm_QLLL_QSAT_finrank_inf_liftL_liftR
import Mathlib

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
@[simp] theorem liftR_top :
    liftR (⊤ : Submodule ℂ (B → ℂ)) = (⊤ : Submodule ℂ ((A × B) → ℂ)) := by
  simp [liftR]

omit [Fintype A] [DecidableEq A] [DecidableEq B] in
theorem finrank_liftL [Finite A] (Y : Submodule ℂ (A → ℂ)) :
    Module.finrank ℂ (liftL Y : Submodule ℂ ((A × B) → ℂ))
      = Module.finrank ℂ Y * Fintype.card B := by
  have h := finrank_inf_liftL_liftR Y (⊤ : Submodule ℂ (B → ℂ))
  rw [liftR_top, inf_top_eq] at h
  rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]

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

theorem finrank_lift (Y : Submodule ℂ (HIn S)) :
    Module.finrank ℂ (lift S Y)
      = Module.finrank ℂ (liftL Y : Submodule ℂ ((CfgIn S × CfgOut S) → ℂ)) := by
  rw [lift_eq_map_liftL]
  exact ((splitEquiv S).submoduleMap (liftL Y)).finrank_eq.symm

theorem finrank_H (n : ℕ) (S : Finset (Fin n)) :
    Module.finrank ℂ (H n) = Fintype.card (CfgIn S) * Fintype.card (CfgOut S) := by
  rw [Module.finrank_fintype_fun_eq_card, ← Fintype.card_prod]
  exact Fintype.card_congr (cfgEquiv S)

/-! ### The complementary side

`CfgOut S` and `CfgIn Sᶜ` carry the same data, as do `CfgIn S` and `CfgOut Sᶜ`,
so a subspace supported on `Sᶜ` is a right lift for the splitting at `S`. -/

end Transport

/-! ## Corollary 16: k-QSAT

The combinatorial half is identical to the classical case in `QuantumLocalLemma.Classical.KSAT`:
constraints on `k` qubits each, every qubit touched by at most `D` constraints,
so each constraint overlaps at most `k (D - 1)` others.
-/

end QLLL.QSAT


section

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem solution (S : Finset (Fin n)) (Y : Submodule ℂ (HIn S)) :
    relDim (lift S Y) = (Module.finrank ℂ Y : ℝ) / (Fintype.card (CfgIn S) : ℝ) := by
  have h1 := finrank_lift (S := S) Y
  rw [finrank_liftL] at h1
  have hcA : (Fintype.card (CfgIn S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (CfgIn S) := Fintype.card_pos
    positivity
  have hcB : (Fintype.card (CfgOut S) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (CfgOut S) := Fintype.card_pos
    positivity
  simp only [relDim, h1, finrank_H n S]
  push_cast
  field_simp

end
