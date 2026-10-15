-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:09.334383+00:00
-- url     : https://prove2.me/submissions/9e0d6284-d782-471c-aaa8-9e829296f8e4

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_meets
import Theorems.Thm_ThreeSum_CyclicFold_cyclic_correlation

namespace Finset
end Finset
namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightCyclic
end ThreeSum.LightCyclic
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightCyclic
end ThreeSum1960614.Machine.ThreeSum.LightCyclic
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

namespace ThreeSum1960614.Machine

/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial

























/-- Splitting at a coefficient boundary is exact, also for padded short lists. -/
theorem asPolynomial_split (n : ℕ) (as : List ℤ) :
    _root_.ThreeSum.Karatsuba.asPolynomial as = _root_.ThreeSum.Karatsuba.asPolynomial (as.take n) + X ^ n * _root_.ThreeSum.Karatsuba.asPolynomial (as.drop n) := by
  induction n generalizing as with
  | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | succ n ih =>
    cases as with
    | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
    | cons a as =>
      simp only [List.take_succ_cons, List.drop_succ_cons, _root_.ThreeSum.Karatsuba.asPolynomial, pow_succ]
      rw [ih as]
      ring











/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/





















end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Coefficient and intermediate-value bounds for the array realization -/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial
open scoped _root_.BigOperators

@[simp] theorem asPolynomial_coeff (as : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as).coeff j = as.getD j 0 := by
  induction as generalizing j with
  | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as ih =>
    cases j with
    | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
    | succ j =>
      rw [_root_.ThreeSum.Karatsuba.asPolynomial, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X_mul, ih]
      simp



























end ThreeSum.Karatsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Folding a dense polynomial product into a cyclic convolution

The product of two vectors of length at most `p` has only two possible
contributions to an output residue `r < p`: coefficients `r` and `r+p`.
The double sum below specifies the answer; the implementation obtains it
by one fast product and a linear pass over the output coefficients.
-/

namespace ThreeSum.CyclicFold
open _root_.ThreeSum.CyclicFold


open _root_.Finset
open _root_.Polynomial
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open scoped _root_.BigOperators

theorem asPolynomial_sum (as : List ℤ) (p : ℕ) (ha : as.length ≤ p) :
    _root_.ThreeSum.Karatsuba.asPolynomial as = ∑ i ∈ Finset.range p, monomial i (as.getD i 0) := by
  apply Polynomial.ext
  intro k
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, finsetSum_coeff, coeff_monomial]
  by_cases hk : k < p
  · simp [hk, eq_comm]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [hk, eq_comm]

theorem product_coeff_double (as bs : List ℤ) (p : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (r : ℕ) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff r =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if i + j = r then as.getD i 0 * bs.getD j 0 else 0 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_sum as p ha, _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_sum bs p hb]
  simp only [sum_mul_sum, finsetSum_coeff, monomial_mul_monomial, coeff_monomial]

theorem mod_indicator {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p)
    (w : ℤ) :
    (if i + j = r then w else 0) + (if i + j = r + p then w else 0) =
      if (i + j) % p = r then w else 0 := by
  by_cases hsum : i + j < p
  · rw [Nat.mod_eq_of_lt hsum]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega



theorem fold_product (as bs : List ℤ) (p r : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (hr : r < p) :
    (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff r +
      (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff (r + p) = _root_.ThreeSum.CyclicFold.cyclic p as bs r := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.product_coeff_double as bs p ha hb, _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.product_coeff_double as bs p ha hb]
  rw [← sum_add_distrib]
  unfold _root_.ThreeSum.CyclicFold.cyclic
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.mod_indicator (mem_range.mp hi) (mem_range.mp hj) hr _



theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (_root_.ThreeSum.CyclicFold.vector p f).length = p := by
  simp [_root_.ThreeSum.CyclicFold.vector]











theorem padTo_length (n : ℕ) (as : List ℤ) (ha : as.length ≤ n) :
    (_root_.ThreeSum.CyclicFold.padTo n as).length = n := by
  simp [_root_.ThreeSum.CyclicFold.padTo, Nat.add_sub_of_le ha]

@[simp] theorem asPolynomial_replicate_zero (n : ℕ) :
    _root_.ThreeSum.Karatsuba.asPolynomial (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | succ n ih => simp [List.replicate_succ, _root_.ThreeSum.Karatsuba.asPolynomial, ih]

theorem asPolynomial_padTo (n : ℕ) (as : List ℤ) :
    _root_.ThreeSum.Karatsuba.asPolynomial (_root_.ThreeSum.CyclicFold.padTo n as) = _root_.ThreeSum.Karatsuba.asPolynomial as := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_split as.length]
  simp [_root_.ThreeSum.CyclicFold.padTo]

theorem coeffBound_padTo {as : List ℤ} {U : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.padTo n as) U := by
  intro j
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_padTo, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff]
  exact h j



end ThreeSum.CyclicFold

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba
open _root_.ThreeSum.LightKaratsuba


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial











































section Join

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}



end Join

section BaseCase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end BaseCase













theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ _root_.ThreeSum.LightKaratsuba.wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  nlinarith







section RecursiveExecution

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}



end RecursiveExecution

section CompleteProcedure

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}









end CompleteProcedure

end ThreeSum.LightKaratsuba

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed folding of the verified polynomial product

The ordinary linear array procedure adds coefficients `r` and `r+p` for
each output residue. Its specification is the exact natural cyclic
correlation, including histogram multiplicities.
-/

namespace ThreeSum.LightCyclic
open _root_.ThreeSum.LightCyclic


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem fold_meets {pLinear : ℕ} (hLinear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} {as bs : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src (2*n) dst p)
    (ha : as.length ≤ p) (hb : bs.length ≤ p)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as (U : ℤ)) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs (U : ℤ))
    (hprod : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ src n (_root_.ThreeSum.CyclicFold.padTo n as) (_root_.ThreeSum.CyclicFold.padTo n bs))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pLinear d [src, src+p, dst, p, 1] μ (_root_.ThreeSum.LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) = _root_.ThreeSum.CyclicFold.cyclic p as bs r) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p := by
  have hfirst (r : ℕ) (hr : r < p) :
      μ (src+r) = (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff r := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_padTo] using hprod r (by omega)
  have hsecond (r : ℕ) (hr : r < p) :
      μ (src+p+r) = (_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff (r+p) := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_padTo, Nat.add_assoc, Nat.add_comm p r] using
      hprod (r+p) (by omega)
  have hc (r : ℕ) :
      |(_root_.ThreeSum.Karatsuba.asPolynomial as * _root_.ThreeSum.Karatsuba.asPolynomial bs).coeff r| ≤ (2*p*U^2 : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound ha hb hA hB r
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d) (μ := μ)
    (srcA := src) (srcB := src+p) (dst := dst) (n := p) (U := 2*p*U^2) (c := 1)
    hLinear hw (by omega) (by omega) hdst (Or.inr (by omega)) (Or.inr (by omega))
    (by norm_num) (by push_cast; nlinarith) (by
      intro r hr
      rw [hfirst r hr, hsecond r hr]
      exact ⟨hc r, hc (r+p)⟩)
  apply h.mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr, one_mul, hfirst r hr, hsecond r hr]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.fold_product as bs p r ha hb hr

theorem fold_correlation_meets {pLinear : ℕ}
    (hLinear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src (2*n) dst p)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p F) (U : ℤ))
    (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z))) (U : ℤ))
    (hprod : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ src n (_root_.ThreeSum.CyclicFold.padTo n (_root_.ThreeSum.CyclicFold.vector p F))
      (_root_.ThreeSum.CyclicFold.padTo n (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pLinear d [src, src+p, dst, p, 1] μ (_root_.ThreeSum.LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (_root_.ThreeSum.Balancing.correlation F H (r : ZMod p) : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.fold_meets hLinear hw hpn hsrc hdst hsep
    (le_of_eq (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length _ _)) (le_of_eq (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length _ _)) hA hB hprod hword).mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr]
  exact _root_.ThreeSum.CyclicFold.cyclic_correlation F H r hr

















end ThreeSum.LightCyclic

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCyclic
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets__implementation_2493479502 {pThis pMultiply pHalf pLinear pFill : ℕ}
    (hThis : P[pThis]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body pMultiply pLinear))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p F)))
    (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))))
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p F) (U : ℤ))
    (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : _root_.Light.Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pThis d [2^k, a, b, prod, dst, work, p] μ (_root_.ThreeSum.LightCyclic.combinedTime k p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (_root_.ThreeSum.Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by
  have hn : 0 < (2 : ℕ)^k := Nat.pow_pos (by decide)
  have hAlen : (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p F)).length = 2^k :=
    _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.padTo_length _ _ (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]; exact hpn)
  have hBlen : (_root_.ThreeSum.CyclicFold.padTo (2^k) (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))).length = 2^k :=
    _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.padTo_length _ _ (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]; exact hpn)
  have hfoldword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word := by
    have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ten_temp_le_word (2^k) U hn
    have hpU := Nat.mul_le_mul_right (U^2) (Nat.mul_le_mul_left 4 hpn)
    have ht' : 4*p*U^2 ≤ _root_.ThreeSum.LightKaratsuba.wordBound (2^k) U := by nlinarith
    exact (by exact_mod_cast ht' : 4 * (p : ℤ) * (U : ℤ)^2 ≤
      (LightKaratsuba.wordBound (2^k) U : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hThis
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.body _root_.ThreeSum.LightCyclic.combinedTime
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.coeffBound_padTo hA (2 ^ k)) (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.coeffBound_padTo hB (2 ^ k)) haf hbf hpf hspace hword (d + 1) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.coeffBound_padTo hA (2 ^ k)) (_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.coeffBound_padTo hB (2 ^ k)) haf hbf hpf hspace hword (d + 1) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro res μ₁ hK; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn (by omega) (by omega) hsep hA hB hK.1 hfoldword) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightCyclic.fold_correlation_meets C.linear (μ := μ₁) (n := 2 ^ k) F H hw hpn (by omega) (by omega) hsep hA hB hK.1 hfoldword) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro res₂ μ₂ hF; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hF.1, ?_⟩
  intro j hj hpj hdj
  exact (hF.2 j hdj).trans (hK.2 j ⟨hj, hpj⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets__implementation_2493479502) := (@ThreeSum1960614.Machine.ThreeSum.LightCyclic.correlation_meets__implementation_2493479502)

#print axioms solution
