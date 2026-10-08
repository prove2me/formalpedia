-- Prove2me | solution 1 for QLLL.QSAT.satisfiable_of_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:57:00.003616+00:00
-- url     : https://prove2.me/submissions/ecdd9646-6b21-4aaf-943c-b721b828e7a5

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Projector
import Theorems.Thm_QLLL_QSAT_inf_lift_ne_bot
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


-- inline helpers from QuantumLocalLemma.Quantum.KQSAT.Projector
/-
Copyright (c) 2026 Or Sattath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Or Sattath
-/

/-!
# Physical projectors and a k-QSAT instance

`QuantumLocalLemma.Quantum.KQSAT.Basic` proves Corollary 16 with the support and dimension facts as
*hypotheses*: it assumes each constraint subspace is supported on its qubit set
and has large enough relative dimension. That is the content of the corollary but
not a formulation of k-QSAT, because no projector appears anywhere.

This file supplies the missing layer.

* `exists_selfAdjoint_isIdempotentElem` : every subspace is the range of a
  *physical* projector, an idempotent and self-adjoint matrix, namely the
  orthogonal projection onto it. So projectors here are quantum projectors, not
  merely algebraic idempotents.
* `finrank_ker_mulVecLin` : rank-nullity, giving the dimension of a satisfying
  space from the rank of its projector.
* `QSATInstance` and `QSATInstance.Satisfiable` : a k-QSAT instance is a family
  of projectors, each acting on `k` qubits, and it is satisfiable when some
  nonzero state is annihilated by all of them.
* `satisfiable_of_degree_le` : Corollary 16 with support and dimension *derived*
  from the projectors rather than assumed.
-/

namespace QLLL.QSAT

open scoped Matrix Kronecker
open WithLp (toLp ofLp)

section IdempotentKernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Rank-nullity: the satisfying space of a matrix has dimension the codimension
of its range. -/
theorem finrank_ker_mulVecLin (p : Matrix ι ι ℂ) :
    Module.finrank ℂ (LinearMap.ker p.mulVecLin) = Fintype.card ι - p.rank := by
  have h := LinearMap.finrank_range_add_finrank_ker p.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Matrix.rank]
  omega

end IdempotentKernel

/-! ## Frustration-freeness

The zero-energy space of a sum of physical projectors is exactly the set of
states satisfying every constraint. This is what links `Satisfiable` below to
the Hamiltonian phrasing of QSAT.
-/

section FrustrationFree

open scoped ComplexOrder

end FrustrationFree

/-! ## Amplifying a local projector to the whole space

A `k`-QSAT constraint is a projector on the `k` qubits it acts on. To write the
Hamiltonian as a single operator these have to be amplified to the common space
`H n`, which is tensoring with the identity on the other qubits.
-/

section Amplify

variable {n : ℕ} {S : Finset (Fin n)} {p : Matrix (CfgIn S) (CfgIn S) ℂ}

end Amplify

/-! ## A k-QSAT instance -/

variable {n : ℕ}

namespace QSATInstance

variable {k : ℕ}

end QSATInstance

/-! ## The Hamiltonian formulation

QSAT is normally posed as: is the local Hamiltonian `H = ∑ Πᵢ` frustration free,
i.e. does it have a zero-energy state? The results above make that equivalent to
the subspace statement used for the local lemma.
-/

namespace QSATInstance

variable {k : ℕ}

end QSATInstance

end QLLL.QSAT


section

open QLLL
open QLLL.QSAT
open scoped Matrix Kronecker
open WithLp (toLp ofLp)
variable {n : ℕ}

theorem solution {k r D' : ℕ} (I : QSATInstance n k)
    (hrank : ∀ i, (I.proj i).rank ≤ r)
    (hdeg : ∀ v : Fin n,
      (Finset.univ.filter fun i => v ∈ I.qubits i).card ≤ D' + 1)
    (hp : ((r : ℝ) / 2 ^ k) * Real.exp 1 * (((k * D' : ℕ) : ℝ) + 1) ≤ 1) :
    I.Satisfiable := by
  refine inf_lift_ne_bot (Sq := I.qubits)
    (Y := fun i => LinearMap.ker (I.proj i).mulVecLin) (r := r)
    I.card_qubits ?_ hdeg hp
  intro i
  have h1 : Module.finrank ℂ (LinearMap.ker (I.proj i).mulVecLin)
      = Fintype.card (CfgIn (I.qubits i)) - (I.proj i).rank :=
    finrank_ker_mulVecLin _
  have h2 := hrank i
  rw [h1, card_cfgIn, I.card_qubits i]
  omega

end
