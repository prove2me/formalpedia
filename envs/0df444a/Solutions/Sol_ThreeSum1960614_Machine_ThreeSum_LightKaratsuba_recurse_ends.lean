-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:49.145789+00:00
-- url     : https://prove2.me/submissions/cca2f5b5-0de6-4c90-9176-da874ad77dc2

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_half_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_Karatsuba_product_coeff_bound
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_join_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_joined_product

namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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









@[simp] theorem length_plus (as bs : List ℤ) :
    (_root_.ThreeSum.Karatsuba.plus as bs).length = max as.length bs.length := by
  induction as generalizing bs with
  | nil => simp [_root_.ThreeSum.Karatsuba.plus]
  | cons a as ih =>
    cases bs with
    | nil => simp [_root_.ThreeSum.Karatsuba.plus]
    | cons b bs => simpa [_root_.ThreeSum.Karatsuba.plus, Nat.succ_max_succ] using congrArg Nat.succ (ih bs)







@[simp] theorem asPolynomial_plus (as bs : List ℤ) :
    _root_.ThreeSum.Karatsuba.asPolynomial (_root_.ThreeSum.Karatsuba.plus as bs) = _root_.ThreeSum.Karatsuba.asPolynomial as + _root_.ThreeSum.Karatsuba.asPolynomial bs := by
  induction as generalizing bs with
  | nil => simp [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial]
    | cons b bs =>
      simp only [_root_.ThreeSum.Karatsuba.plus, _root_.ThreeSum.Karatsuba.asPolynomial, ih, map_add]
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
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]







theorem Seg.take (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (k : ℕ) : _root_.ThreeSum1960614.Machine.Light.Seg μ a (l.take k) := fun i hi => by
  have hi' : i < l.length := by simp at hi; omega
  rw [List.getElem_take, h i hi']

theorem Seg.drop (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (k : ℕ) : _root_.ThreeSum1960614.Machine.Light.Seg μ (a + k) (l.drop k) := fun i hi => by
  have hi' : k + i < l.length := by simp at hi; omega
  rw [List.getElem_drop, ← h _ hi', Nat.add_assoc]

/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















































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

@[simp] theorem plus_getD (as bs : List ℤ) (j : ℕ) :
    (_root_.ThreeSum.Karatsuba.plus as bs).getD j 0 = as.getD j 0 + bs.getD j 0 := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, Polynomial.coeff_add] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) (_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_plus as bs)





theorem coeffBound_nonneg {as : List ℤ} {U : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) : 0 ≤ U :=
  (abs_nonneg _).trans (h 0)

theorem CoeffBound.of_mem {as : List ℤ} {U : ℤ} (hU : 0 ≤ U)
    (hm : ∀ x ∈ as, |x| ≤ U) : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U := by
  intro j
  by_cases hj : j < as.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact hm _ (List.getElem_mem hj)
  · rw [List.getD_eq_default _ _ (by omega), abs_zero]
    exact hU

theorem CoeffBound.mem {as : List ℤ} {U x : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U)
    (hx : x ∈ as) : |x| ≤ U := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  simpa only [List.getD_eq_getElem _ _ hj] using h j

theorem CoeffBound.take {as : List ℤ} {U : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (as.take n) U :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound.of_mem (_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_take hx))

theorem CoeffBound.drop {as : List ℤ} {U : ℤ} (h : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (as.drop n) U :=
  _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound.of_mem (_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.coeffBound_nonneg h) (fun x hx => h.mem (List.mem_of_mem_drop hx))

theorem CoeffBound.plus {as bs : List ℤ} {U V : ℤ}
    (ha : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (hb : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs V) : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.Karatsuba.plus as bs) (U + V) := by
  intro j
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.plus_getD]
  exact (abs_add_le _ _).trans (add_le_add (ha j) (hb j))









end ThreeSum.Karatsuba

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







theorem wordBound_monoU {n U V : ℕ} (hUV : U ≤ V) : _root_.ThreeSum.LightKaratsuba.wordBound n U ≤ _root_.ThreeSum.LightKaratsuba.wordBound n V := by
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U + 1 ≤ V + 1) 2)

theorem wordBound_child (m U : ℕ) : _root_.ThreeSum.LightKaratsuba.wordBound m (2 * U) ≤ _root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U := by
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  have hu : (2 * U + 1) ^ 2 ≤ (2 * (U + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 128 * m ^ 3 * (2 * (U + 1)) ^ 2 := Nat.mul_le_mul_left _ hu
    _ ≤ _ := by ring_nf; omega

theorem wordBound_ge_twice (n U : ℕ) (hn : 0 < n) : 2 * U ≤ _root_.ThreeSum.LightKaratsuba.wordBound n U := by
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hu : U ≤ (U + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left ((U + 1) ^ 2) hn3
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  nlinarith

theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ _root_.ThreeSum.LightKaratsuba.wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  nlinarith

theorem linear_plus_segment {μ μ' : ℕ → ℤ} {a b out n : ℕ} {as bs : List ℤ}
    (ha : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hb : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs) (hAlen : as.length = n) (hBlen : bs.length = n)
    (hwrite : ∀ i < n, μ' (out + i) = μ (a + i) + 1 * μ (b + i)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ' out (_root_.ThreeSum.Karatsuba.plus as bs) := by
  intro i hi
  have hin : i < n := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.length_plus, hAlen, hBlen, max_self] using hi
  rw [← List.getD_eq_getElem _ 0 hi, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.plus_getD,
    ← ha.getD (by omega : i < as.length) 0, ← hb.getD (by omega : i < bs.length) 0]
  simpa only [one_mul] using hwrite i hin

theorem ProductAt.bound {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ} {U : ℤ}
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as U) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs U) :
    ∀ j < 2 * n, |μ (out + j)| ≤ 2 * (n : ℤ) * U ^ 2 := by
  intro j hj
  rw [hp j hj]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.product_coeff_bound ha hb hA hB j

theorem ProductAt.congr {μ μ' : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ out n as bs)
    (he : ∀ j < 2 * n, μ' (out + j) = μ (out + j)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ' out n as bs := fun j hj => (he j hj).trans (hp j hj)

section RecursiveExecution

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}



end RecursiveExecution

section CompleteProcedure

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}









end CompleteProcedure

end ThreeSum.LightKaratsuba

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}
section

set_option maxHeartbeats 2000000 in
theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends__implementation_43c26a5856 (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill)
    {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word)
    (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as (U : ℤ)) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work)
    (hof : out + 2 * (2 * m) ≤ work) (hspace : work + 8 * (2 * m) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih : ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
      as'.length = m → bs'.length = m → _root_.ThreeSum1960614.Machine.Light.Seg μ' a' as' → _root_.ThreeSum1960614.Machine.Light.Seg μ' b' bs' →
      _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as' (U' : ℤ) → _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs' (U' : ℤ) →
      a' + m ≤ work' → b' + m ≤ work' → out' + 2 * m ≤ work' →
      work' + 8 * m ≤ lim.space → (_root_.ThreeSum.LightKaratsuba.wordBound m U' : ℤ) ≤ lim.word →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (_root_.ThreeSum.LightKaratsuba.time k)
        (fun _ μ'' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ' out' m work' as' bs' μ'')) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurseBody pSelf pHalf pLinear pFill)
      ⟨_root_.Light.frame [2 * m, a, b, out, work], μ⟩ (_root_.ThreeSum.LightKaratsuba.time (k + 1) - 4)
      (fun σ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ out (2 * m) work as bs σ'.mem) := by
  have hm : 0 < m := hmPow ▸ Nat.pow_pos (by decide)
  have hAU0 := hA.take m
  have hAU1 := hA.drop m
  have hBU0 := hB.take m
  have hBU1 := hB.drop m
  have hAs : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.Karatsuba.plus (as.take m) (as.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hAU0.plus hAU1
  have hBs : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.Karatsuba.plus (bs.take m) (bs.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hBU0.plus hBU1
  have ha0 : (as.take m).length = m := by simp only [List.length_take, hAlen]; omega
  have ha1 : (as.drop m).length = m := by simp only [List.length_drop, hAlen]; omega
  have hb0 : (bs.take m).length = m := by simp only [List.length_take, hBlen]; omega
  have hb1 : (bs.drop m).length = m := by simp only [List.length_drop, hBlen]; omega
  have has : (_root_.ThreeSum.Karatsuba.plus (as.take m) (as.drop m)).length = m := by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.length_plus, ha0, ha1, max_self]
  have hbs : (_root_.ThreeSum.Karatsuba.plus (bs.take m) (bs.drop m)).length = m := by simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.length_plus, hb0, hb1, max_self]
  have hword2 : 2 * (U : ℤ) ≤ lim.word := by
    have hh : 2 * (U : ℤ) ≤ _root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.wordBound_ge_twice (2 * m) U (by omega)
    exact hh.trans hword
  have hchild2 : (_root_.ThreeSum.LightKaratsuba.wordBound m (2 * U) : ℤ) ≤ lim.word := by
    have hc : (_root_.ThreeSum.LightKaratsuba.wordBound m (2 * U) : ℤ) ≤ _root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.wordBound_child m U
    exact hc.trans hword
  have hchild1 : (_root_.ThreeSum.LightKaratsuba.wordBound m U : ℤ) ≤ lim.word := by
    have hc : (_root_.ThreeSum.LightKaratsuba.wordBound m U : ℤ) ≤ _root_.ThreeSum.LightKaratsuba.wordBound m (2 * U) := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.wordBound_monoU (n := m) (by omega : U ≤ 2 * U)
    exact hc.trans hchild2
  have hhalfeq : (2 * m + 1) / 2 = m := by omega
  have hhalfword : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (show 2 * m + 1 ≤ lim.space by omega)
    exact hh.trans hw
  have hhalf := _root_.ThreeSum1960614.Machine.Light.half_meets (lim := lim) (d := d + 1) C.half μ (h := 2 * m) hhalfword
  simp only [_root_.Light.halfTime, hhalfeq] at hhalf
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurseBody
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hhalf _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hhalf ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time] <;> omega)
     on_goal -1 => (rintro _ μ₀ ⟨rfl, hμ₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₀
  have hsA0 := hAseg.take m
  have hsA1 := hAseg.drop m
  have hsumA := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ) (srcA := a) (srcB := a + m) (dst := work + 3 * (2 * m))
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsA0.getD (by omega) 0]; exact hAU0 i,
      by rw [hsA1.getD (by omega) 0]; exact hAU1 i⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsumA _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsumA ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨hrA, hkA⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hsuma := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.linear_plus_segment hsA0 hsA1 ha0 ha1 hrA
  have hBseg1 : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ b bs := hBseg.congr (fun i hi => hkA _ (by omega))
  have hsB0 := hBseg1.take m
  have hsB1 := hBseg1.drop m
  have hsumB := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ₁) (srcA := b) (srcB := b + m) (dst := work + 3 * (2 * m) + m)
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsB0.getD (by omega) 0]; exact hBU0 i,
      by rw [hsB1.getD (by omega) 0]; exact hBU1 i⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsumB _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsumB ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₂ ⟨hrB, hkB⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hsumb := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.linear_plus_segment hsB0 hsB1 hb0 hb1 hrB
  have hsuma2 : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ (work + 3 * (2 * m)) (_root_.ThreeSum.Karatsuba.plus (as.take m) (as.drop m)) :=
    hsuma.congr (fun i hi => hkB _ (by omega))
  have hAseg2 : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ a as := hAseg.congr (fun i hi => (hkB _ (by omega)).trans (hkA _ (by omega)))
  have hBseg2 : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ b bs := hBseg1.congr (fun i hi => hkB _ (by omega))
  have hprod0 := ih a b work (work + 4 * (2 * m)) U (as.take m) (bs.take m) μ₂
    ha0 hb0 (hAseg2.take m) (hBseg2.take m) hAU0 hBU0
    (by omega) (by omega) (by omega) (by omega) hchild1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hprod0 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hprod0 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₃ ⟨hp0, hkp0⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hAseg3 : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ a as := hAseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hBseg3 : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ b bs := hBseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hprod2 := ih (a + m) (b + m) (work + 2 * m) (work + 4 * (2 * m)) U
    (as.drop m) (bs.drop m) μ₃ ha1 hb1 (hAseg3.drop m) (hBseg3.drop m) hAU1 hBU1
    (by omega) (by omega) (by omega) (by omega) hchild1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hprod2 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hprod2 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₄ ⟨hp2, hkp2⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hp04 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ₄ work m (as.take m) (bs.take m) :=
    hp0.congr (fun j hj => hkp2 _ ⟨by omega, by omega⟩)
  have hsuma4 : _root_.ThreeSum1960614.Machine.Light.Seg μ₄ (work + 3 * (2 * m)) (_root_.ThreeSum.Karatsuba.plus (as.take m) (as.drop m)) :=
    hsuma2.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hsumb4 : _root_.ThreeSum1960614.Machine.Light.Seg μ₄ (work + 3 * (2 * m) + m) (_root_.ThreeSum.Karatsuba.plus (bs.take m) (bs.drop m)) :=
    hsumb.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hprodm := ih (work + 3 * (2 * m)) (work + 3 * (2 * m) + m)
    (work + 2 * (2 * m)) (work + 4 * (2 * m)) (2 * U)
    (_root_.ThreeSum.Karatsuba.plus (as.take m) (as.drop m)) (_root_.ThreeSum.Karatsuba.plus (bs.take m) (bs.drop m)) μ₄
    has hbs hsuma4 hsumb4 hAs hBs
    (by omega) (by omega) (by omega) (by omega) hchild2
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hprodm _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hprodm ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₅ ⟨hpm, hkpm⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hp05 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ₅ work m (as.take m) (bs.take m) :=
    hp04.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have hp25 : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ₅ (work + 2 * m) m (as.drop m) (bs.drop m) :=
    hp2.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have htword : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ _root_.ThreeSum.LightKaratsuba.wordBound (2 * m) U := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ten_temp_le_word (2 * m) U (by omega)
    exact hh.trans hword
  have htemp : ∀ i < 2 * m,
      |μ₅ (work + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * m + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * (2 * m) + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) := by
    intro i hi
    have h₀ := hp05.bound ha0.le hb0.le hAU0 hBU0 i hi
    have h₂ := hp25.bound ha1.le hb1.le hAU1 hBU1 i hi
    have hₘ := hpm.bound has.le hbs.le hAs hBs i hi
    push_cast at hₘ ⊢
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    · nlinarith
  refine (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends C.linear C.fill (n := 2 * m) (half := m) (U := 4 * (2 * m) * U ^ 2)
    (by omega) rfl hw hof (by omega) htword htemp hd).mono
      (by (first
           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
               first
               | omega
               | (ring_nf; omega))
           | omega
           |
             (simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
                 first
                 | omega
                 | (ring_nf; omega)))) ?_
  intro σ' hj
  constructor
  · intro j hjj
    exact (hj.1 j hjj).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joined_product rfl hAlen hBlen hp05 hp25 hpm j)
  · intro j hjj
    rw [hj.2 j hjj, hkpm j ⟨by omega, by omega⟩, hkp2 j ⟨by omega, by omega⟩,
      hkp0 j ⟨by omega, by omega⟩, hkB j (by omega), hkA j (by omega)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends__implementation_43c26a5856) := (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends__implementation_43c26a5856)

#print axioms solution
