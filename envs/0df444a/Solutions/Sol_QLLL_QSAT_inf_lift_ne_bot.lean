-- Prove2me | solution 1 for QLLL.QSAT.inf_lift_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:54:22.365646+00:00
-- url     : https://prove2.me/submissions/a3f7c70c-b1d6-4fdb-9e32-eada3c176161

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Theorems.Thm_QLLL_QSAT_inf_ne_bot_of_degree_le
import Theorems.Thm_QLLL_QSAT_relDim_lift
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

end Split

/-! ## Transporting the product rule to the qubit splitting -/

section Transport

variable {n : ℕ} {S : Finset (Fin n)}

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


section

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}

theorem solution {m : ℕ} {Sq : Fin m → Finset (Fin n)}
    {Y : (i : Fin m) → Submodule ℂ (HIn (Sq i))} {k r D' : ℕ}
    (hcard : ∀ i, (Sq i).card = k)
    (hrank : ∀ i, 2 ^ k - r ≤ Module.finrank ℂ (Y i))
    (hdeg : ∀ v : Fin n, (univ.filter fun i => v ∈ Sq i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    univ.inf (fun i => lift (Sq i) (Y i)) ≠ ⊥ := by
  refine inf_ne_bot_of_degree_le (Sq := Sq) (p := (r : ℝ) / 2 ^ k)
    (fun i => ⟨Y i, rfl⟩) hcard ?_ hdeg hp
  intro i
  have hr : ((2 ^ k - r : ℕ) : ℝ) ≤ (Module.finrank ℂ (Y i) : ℝ) := by
    exact_mod_cast hrank i
  have hge : (2:ℝ) ^ k - (r : ℝ) ≤ (Module.finrank ℂ (Y i) : ℝ) := by
    rcases le_total r (2 ^ k) with h | h
    · rw [Nat.cast_sub h] at hr
      push_cast at hr
      linarith
    · have hle : ((2 ^ k : ℕ) : ℝ) ≤ (r : ℝ) := by exact_mod_cast h
      have h0 : (0:ℝ) ≤ (Module.finrank ℂ (Y i) : ℝ) := by positivity
      push_cast at hle
      linarith
  rw [relDim_lift, card_cfgIn, hcard i]
  have h2 : (0:ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ h2]
  push_cast
  have h2' : (0:ℝ) < (2:ℝ) ^ k := by positivity
  field_simp
  linarith [hge]

end
