-- Prove2me | solution 1 for QLLL.QSAT.finrank_inf_liftL_liftR
-- status  : ACCEPTED   (prove)
-- author  : @sattath
-- created : 2026-10-06T17:48:09.850139+00:00
-- url     : https://prove2.me/submissions/1f8792d3-1741-4bee-b06e-4968348c2e99

import Definitions.Def_QLLL_LocalLemma_Basic
import Definitions.Def_QLLL_Quantum_KQSAT_Basic
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

/-- A Kronecker product of idempotents is idempotent. -/
theorem isIdempotentElem_kronecker {p : Matrix ι ι ℂ} {q : Matrix κ κ ℂ}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    IsIdempotentElem (p ⊗ₖ q) := by
  rw [IsIdempotentElem, ← Matrix.mul_kronecker_mul, hp, hq]

/-- Every submodule of a vector space is the range of an idempotent
endomorphism: take a complement and project along it. -/
theorem exists_isIdempotentElem_range_eq {E : Type*} [AddCommGroup E] [Module ℂ E]
    (Y : Submodule ℂ E) :
    ∃ e : Module.End ℂ E, IsIdempotentElem e ∧ LinearMap.range e = Y := by
  obtain ⟨Y', hY'⟩ := Y.exists_isCompl
  exact ⟨_, (Y.isIdempotentElemEquiv.symm (Y.isComplEquivProj ⟨Y', hY'⟩)).2⟩

/-- Matrix form: every submodule of `ι → ℂ` is the range of an idempotent
matrix. -/
theorem exists_isIdempotentElem_matrix {ι : Type*} [Fintype ι]
    (Y : Submodule ℂ (ι → ℂ)) :
    ∃ p : Matrix ι ι ℂ, IsIdempotentElem p ∧ LinearMap.range p.mulVecLin = Y := by
  classical
  obtain ⟨e, he, hr⟩ := exists_isIdempotentElem_range_eq Y
  refine ⟨Matrix.toLinAlgEquiv'.symm e, he.map Matrix.toLinAlgEquiv'.symm, ?_⟩
  rwa [show (Matrix.toLinAlgEquiv'.symm e).mulVecLin = e from
    Matrix.toLinAlgEquiv'.apply_symm_apply e]

/-- For an idempotent endomorphism of a finite dimensional space, the dimension
of the range equals the trace.

This is `LinearMap.IsProj.trace` in Mathlib, reached through
`IsIdempotentElem.isProj_range`. -/
theorem finrank_range_eq_trace_of_isIdempotentElem {E : Type*} [AddCommGroup E]
    [Module ℂ E] [FiniteDimensional ℂ E] {e : Module.End ℂ E}
    (he : IsIdempotentElem e) :
    (Module.finrank ℂ (LinearMap.range e) : ℂ) = LinearMap.trace ℂ E e :=
  (LinearMap.IsIdempotentElem.isProj_range _ he).trace.symm

/-- For an idempotent matrix, rank equals trace. -/
theorem rank_eq_trace_of_isIdempotentElem {p : Matrix ι ι ℂ}
    (hp : IsIdempotentElem p) : (p.rank : ℂ) = p.trace := by
  classical
  have he : IsIdempotentElem (Matrix.toLinAlgEquiv' p) :=
    _root_.IsIdempotentElem.map hp (Matrix.toLinAlgEquiv' (R := ℂ) (n := ι))
  have h1 : Matrix.toLinAlgEquiv' p = Matrix.mulVecLin p := rfl
  rw [Matrix.rank, ← h1, finrank_range_eq_trace_of_isIdempotentElem he]
  exact Matrix.trace_toLin'_eq p

/-- The rank of a Kronecker product of idempotents multiplies. This is the
dimension count behind Lemma 11: a constraint on `S` and a constraint on `Sᶜ`
cut out a subspace whose dimension is the product. -/
theorem rank_kronecker_of_isIdempotentElem
    {p : Matrix ι ι ℂ} {q : Matrix κ κ ℂ}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    (((p ⊗ₖ q).rank : ℂ)) = (p.rank : ℂ) * (q.rank : ℂ) := by
  rw [rank_eq_trace_of_isIdempotentElem (isIdempotentElem_kronecker hp hq),
    Matrix.trace_kronecker,
    rank_eq_trace_of_isIdempotentElem hp, rank_eq_trace_of_isIdempotentElem hq]

/-- For commuting idempotents the range of the product is the intersection of
the ranges. Applied to `(1 - p) ⊗ₖ 1` and `1 ⊗ₖ (1 - q)`, whose product is
`(1 - p) ⊗ₖ (1 - q)`, this is what expresses the satisfying space of two
constraints on complementary sets of qubits as a single Kronecker product. -/
theorem range_mul_of_commute {E : Type*} [AddCommGroup E] [Module ℂ E]
    {e f : Module.End ℂ E} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (h : Commute e f) :
    LinearMap.range (e * f) = LinearMap.range e ⊓ LinearMap.range f := by
  have hfix : ∀ (g : Module.End ℂ E), IsIdempotentElem g →
      ∀ x ∈ LinearMap.range g, g x = x := by
    intro g hg x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    rw [← Module.End.mul_apply, hg]
  refine le_antisymm (le_inf ?_ ?_) ?_
  · intro x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨f v, (Module.End.mul_apply e f v).symm⟩
  · intro x hx
    obtain ⟨v, rfl⟩ := LinearMap.mem_range.mp hx
    refine LinearMap.mem_range.mpr ⟨e v, ?_⟩
    rw [h.eq, Module.End.mul_apply]
  · intro x hx
    obtain ⟨hxe, hxf⟩ := Submodule.mem_inf.mp hx
    refine LinearMap.mem_range.mpr ⟨x, ?_⟩
    rw [Module.End.mul_apply, hfix f hf x hxf, hfix e he x hxe]

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

omit [DecidableEq A] in
theorem mulVec_kronecker_one (p : Matrix A A ℂ) (f : (A × B) → ℂ) (a : A) (b : B) :
    (p ⊗ₖ (1 : Matrix B B ℂ)).mulVec f (a, b) = p.mulVec (colSlice b f) a := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

omit [DecidableEq B] in
theorem mulVec_one_kronecker (q : Matrix B B ℂ) (f : (A × B) → ℂ) (a : A) (b : B) :
    ((1 : Matrix A A ℂ) ⊗ₖ q).mulVec f (a, b) = q.mulVec (rowSlice a f) b := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply]

/-- `mulVecLin` is multiplicative, phrased with `Module.End` multiplication. -/
theorem mulVecLin_mul' {ι : Type*} [Fintype ι] (M N : Matrix ι ι ℂ) :
    (M * N).mulVecLin = M.mulVecLin * N.mulVecLin := Matrix.mulVecLin_mul M N

theorem isIdempotentElem_mulVecLin {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℂ} (hM : IsIdempotentElem M) : IsIdempotentElem M.mulVecLin := by
  rw [IsIdempotentElem, ← mulVecLin_mul', hM]

/-- For an idempotent matrix the range of the associated map is its fixed
space. -/
theorem range_mulVecLin_of_isIdempotentElem {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℂ} (hM : IsIdempotentElem M) :
    LinearMap.range M.mulVecLin = LinearMap.eqLocus M.mulVecLin LinearMap.id := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hv
    rw [LinearMap.mem_eqLocus]
    simp only [Matrix.mulVecLin_apply, LinearMap.id_coe, id_eq]
    rw [Matrix.mulVec_mulVec, hM]
  · intro v hv
    rw [LinearMap.mem_eqLocus] at hv
    exact LinearMap.mem_range.mpr ⟨v, hv⟩

omit [DecidableEq A] in
theorem liftL_eq_range {Y : Submodule ℂ (A → ℂ)} {p : Matrix A A ℂ}
    (hp : IsIdempotentElem p) (hY : LinearMap.range p.mulVecLin = Y) :
    liftL Y = LinearMap.range (p ⊗ₖ (1 : Matrix B B ℂ)).mulVecLin := by
  rw [range_mulVecLin_of_isIdempotentElem
    (isIdempotentElem_kronecker hp (one_mul (1 : Matrix B B ℂ)))]
  ext f
  rw [LinearMap.mem_eqLocus]
  simp only [liftL, Submodule.mem_iInf, Submodule.mem_comap, ← hY,
    range_mulVecLin_of_isIdempotentElem hp, LinearMap.mem_eqLocus,
    Matrix.mulVecLin_apply, LinearMap.id_coe, id_eq]
  constructor
  · intro h
    funext c
    obtain ⟨a, b⟩ := c
    rw [mulVec_kronecker_one, h b, colSlice_apply]
  · intro h b
    funext a
    rw [colSlice_apply, ← mulVec_kronecker_one, h]

omit [DecidableEq B] in
theorem liftR_eq_range {W : Submodule ℂ (B → ℂ)} {q : Matrix B B ℂ}
    (hq : IsIdempotentElem q) (hW : LinearMap.range q.mulVecLin = W) :
    liftR W = LinearMap.range ((1 : Matrix A A ℂ) ⊗ₖ q).mulVecLin := by
  rw [range_mulVecLin_of_isIdempotentElem
    (isIdempotentElem_kronecker (one_mul (1 : Matrix A A ℂ)) hq)]
  ext f
  rw [LinearMap.mem_eqLocus]
  simp only [liftR, Submodule.mem_iInf, Submodule.mem_comap, ← hW,
    range_mulVecLin_of_isIdempotentElem hq, LinearMap.mem_eqLocus,
    Matrix.mulVecLin_apply, LinearMap.id_coe, id_eq]
  constructor
  · intro h
    funext c
    obtain ⟨a, b⟩ := c
    rw [mulVec_one_kronecker, h a, rowSlice_apply]
  · intro h a
    funext b
    rw [rowSlice_apply, ← mulVec_one_kronecker, h]

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

end QLLL.QSAT


section

open QLLL
open QLLL.QSAT
open Finset Module
variable {n : ℕ}
open scoped Kronecker
variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem solution [Finite A] [Finite B]
    (Y : Submodule ℂ (A → ℂ)) (W : Submodule ℂ (B → ℂ)) :
    Module.finrank ℂ ((liftL Y ⊓ liftR W : Submodule ℂ ((A × B) → ℂ)))
      = Module.finrank ℂ Y * Module.finrank ℂ W := by
  cases nonempty_fintype A
  cases nonempty_fintype B
  classical
  obtain ⟨p, hp, hpY⟩ := exists_isIdempotentElem_matrix Y
  obtain ⟨q, hq, hqW⟩ := exists_isIdempotentElem_matrix W
  have hpq : (p ⊗ₖ (1 : Matrix B B ℂ)) * ((1 : Matrix A A ℂ) ⊗ₖ q) = p ⊗ₖ q := by
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
  have hqp : ((1 : Matrix A A ℂ) ⊗ₖ q) * (p ⊗ₖ (1 : Matrix B B ℂ)) = p ⊗ₖ q := by
    rw [← Matrix.mul_kronecker_mul, mul_one, one_mul]
  have hcomm : Commute (p ⊗ₖ (1 : Matrix B B ℂ)).mulVecLin
      ((1 : Matrix A A ℂ) ⊗ₖ q).mulVecLin := by
    rw [Commute, SemiconjBy, ← mulVecLin_mul', ← mulVecLin_mul', hpq, hqp]
  have hkey : (liftL Y ⊓ liftR W : Submodule ℂ ((A × B) → ℂ))
      = LinearMap.range ((p ⊗ₖ q : Matrix (A × B) (A × B) ℂ)).mulVecLin := by
    rw [liftL_eq_range hp hpY, liftR_eq_range hq hqW,
      ← range_mul_of_commute
        (isIdempotentElem_mulVecLin
          (isIdempotentElem_kronecker hp (one_mul (1 : Matrix B B ℂ))))
        (isIdempotentElem_mulVecLin
          (isIdempotentElem_kronecker (one_mul (1 : Matrix A A ℂ)) hq)) hcomm,
      ← mulVecLin_mul', hpq]
  have hN : (p ⊗ₖ q : Matrix (A × B) (A × B) ℂ).rank = p.rank * q.rank := by
    exact_mod_cast rank_kronecker_of_isIdempotentElem hp hq
  rw [hkey, ← hpY, ← hqW]
  exact hN

end
