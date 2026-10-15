-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:26:49.475282+00:00
-- url     : https://prove2.me/submissions/ded1b4a9-0c3f-4b84-8daf-d68ddab9bbf4

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBalancedOffset_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCapacity_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidueHistogram_meets

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
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCounts
end ThreeSum1960614.Machine.ThreeSum.ModuloCounts

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
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem count_le (key : ℕ → ℕ) (r i : ℕ) : _root_.ThreeSum.LightHistogram.count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)















end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h















end ThreeSum.LightResidues

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













theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (_root_.ThreeSum.CyclicFold.vector p f).length = p := by
  simp [_root_.ThreeSum.CyclicFold.vector]

theorem vector_getD (p : ℕ) (f : ZMod p → ℕ) (i : ℕ) (hi : i < p) :
    (_root_.ThreeSum.CyclicFold.vector p f).getD i 0 = (f (i : ZMod p) : ℤ) := by
  rw [List.getD_eq_getElem (_root_.ThreeSum.CyclicFold.vector p f) 0 (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]; exact hi)]
  simp only [_root_.ThreeSum.CyclicFold.vector, List.getElem_map, List.getElem_range]









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





end ThreeSum.CyclicFold

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface
open _root_.ThreeSum.KaratsubaInterface


open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Polynomial



theorem le_capacity (p : ℕ) : p ≤ _root_.ThreeSum.KaratsubaInterface.capacity p := Nat.le_pow_clog (by decide) p

























end ThreeSum.KaratsubaInterface

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



/-- Negating the original integers supplies the reversal needed by a
correlation, without a separate reverse-array operation. -/
theorem signedHistogram_neg (p : ℕ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) :
    _root_.ThreeSum.LightResidueHistogram.signedHistogram p (-1) values n z = _root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 values n (-z) := by
  simp only [_root_.ThreeSum.LightResidueHistogram.signedHistogram, _root_.ThreeSum.Histograms.histogram, neg_mul, one_mul, Int.cast_neg,
    neg_eq_iff_eq_neg]



theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold _root_.ThreeSum.LightResidues.residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

theorem residue_eq_iff {p : ℕ} [NeZero p] (c x : ℤ) {r : ℕ} (hr : r < p) :
    _root_.ThreeSum.LightResidues.residue p c x = r ↔ ((c * x : ℤ) : ZMod p) = (r : ZMod p) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  constructor
  · intro h
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod hp, h]
  · intro h
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_zmod hp] at h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp c x),
      ZMod.val_natCast_of_lt hr] using hv

theorem signedHistogram_eq_count {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : r < p) :
    _root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n (r : ZMod p) =
      _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightResidues.residue p c (values i)) r n := by
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram _root_.ThreeSum.Histograms.histogram _root_.ThreeSum.LightHistogram.count
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.residue_eq_iff c (values i) hr]

theorem signed_count_zero {p : ℕ} (hp : 0 < p)
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : p ≤ r) :
    _root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightResidues.residue p c (values i)) r n = 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i hi heq
  change _root_.ThreeSum.LightResidues.residue p c (values i) = r at heq
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp c (values i)
  omega

/-- This equality holds at every index, including the zero padding. -/
theorem padded_histogram_getD {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap r : ℕ) :
    (_root_.ThreeSum.CyclicFold.padTo cap (_root_.ThreeSum.CyclicFold.vector p (_root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n))).getD r 0 =
      (_root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightResidues.residue p c (values i)) r n : ℤ) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff, _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.asPolynomial_padTo, _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_coeff]
  by_cases hr : r < p
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_getD _ _ _ hr, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.signedHistogram_eq_count c values n r hr]
  · rw [List.getD_eq_default _ _ (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]; omega)]
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.signed_count_zero (Nat.pos_of_ne_zero (NeZero.ne p)) c values n r (by omega)]
    rfl

theorem padded_histogram_bound {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.padTo cap (_root_.ThreeSum.CyclicFold.vector p (_root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n))) (n : ℤ) := by
  intro r
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.padded_histogram_getD, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le (fun i => _root_.ThreeSum.LightResidues.residue p c (values i)) r n















end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts
open _root_.ThreeSum.ModuloCounts


open _root_.Finset
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open scoped _root_.BigOperators















theorem signedHistogram_congr {p c n} {a b : ℕ → ℤ}
    (hab : ∀ i < n, a i = b i) :
    _root_.ThreeSum.LightResidueHistogram.signedHistogram p c a n = _root_.ThreeSum.LightResidueHistogram.signedHistogram p c b n := by
  funext z
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram _root_.ThreeSum.Histograms.histogram
  apply sum_congr rfl
  intro i hi
  simp only [hab i (mem_range.mp hi)]



end ThreeSum.ModuloCounts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightOriginalOffset
open _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open scoped _root_.BigOperators
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets__implementation_cb7e924924 {pMain a b nLeft nRight p N free U : ℕ} [NeZero p]
    {μ : ℕ → ℤ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : _root_.ThreeSum.LightOriginalOffset.space free p N U ≤ lim.space) (hword : (_root_.ThreeSum.LightOriginalOffset.word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,nLeft,nRight,p,N,free] μ (_root_.ThreeSum.LightOriginalOffset.time p nLeft nRight U)
      (fun r ν => r = (_root_.ThreeSum.LightOriginalOffset.selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  let q := _root_.ThreeSum.KaratsubaInterface.capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface.le_capacity p
  have hspace' : free+13*q+N+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hkw : (_root_.ThreeSum.LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show _root_.ThreeSum.LightKaratsuba.wordBound q N ≤ _root_.ThreeSum.LightOriginalOffset.word p N U by
      unfold _root_.ThreeSum.LightOriginalOffset.word; change _root_.ThreeSum.LightKaratsuba.wordBound (_root_.ThreeSum.KaratsubaInterface.capacity p) N ≤ _; omega)).trans hword
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*U+4*p+16 ≤ _root_.ThreeSum.LightOriginalOffset.word p N U := by unfold _root_.ThreeSum.LightOriginalOffset.word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hcw : ((2*p+1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  let F := _root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 (fun i => μ (b+i)) nRight
  let H := _root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 (fun i => μ (a+i)) nLeft
  have hHneg : _root_.ThreeSum.LightResidueHistogram.signedHistogram p (-1) (fun i => μ (a+i)) nLeft = (fun z => H (-z)) := by
    funext z
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.signedHistogram_neg p _ _ z
  have hFbound : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p F) (N : ℤ) := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.padded_histogram_bound (p := p) 1 (fun i => μ (b+i)) nRight 0
    simp only [_root_.ThreeSum.CyclicFold.padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnRight)
  have hHbound : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z))) (N : ℤ) := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.padded_histogram_bound (p := p) (-1) (fun i => μ (a+i)) nLeft 0
    simp only [_root_.ThreeSum.CyclicFold.padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnLeft)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.body _root_.ThreeSum.LightOriginalOffset.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.meets C.capacityProc μ hp hcw) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightCapacity.meets C.capacityProc μ hp hcw) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, _root_.ThreeSum.KaratsubaInterface.capacity]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [q, _root_.ThreeSum.KaratsubaInterface.capacity] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, _root_.ThreeSum.KaratsubaInterface.capacity] <;> omega)
     on_goal -1 => (rintro capVal μ₀ ⟨hcapacity, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₀
  subst capVal
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + q) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + 2 * q) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + 3 * q) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + 5 * q) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free + 5 * q + N) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets (d := d + 1) (src := a) (dst := free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c := -1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hLeft) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets (d := d + 1) (src := a) (dst := free + 2 * q) (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c := -1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hLeft) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, _root_.ThreeSum.KaratsubaInterface.capacity]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [q, _root_.ThreeSum.KaratsubaInterface.capacity] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, _root_.ThreeSum.KaratsubaInterface.capacity] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨hLeftSeg, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [hHneg] at hLeftSeg
  have hRightRead (i : ℕ) (hi : i < nRight) : μ₁ (b+i) = μ (b+i) :=
    hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩
  have hRight₁ : ∀ i < nRight, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hRightRead i hi]
    exact hRight i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + q) (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c := 1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hRight₁) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets (d := d + 1) (src := b) (dst := free + q) (codes := free + 5 * q) (work := free + 5 * q + N) (cap := q) (c := 1) C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hRight₁) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, _root_.ThreeSum.KaratsubaInterface.capacity]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [q, _root_.ThreeSum.KaratsubaInterface.capacity] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, _root_.ThreeSum.KaratsubaInterface.capacity] <;> omega)
     on_goal -1 => (rintro _ μ₂ ⟨hRightSeg, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ModuloCounts.signedHistogram_congr (p := p) (c := 1) hRightRead] at hRightSeg
  have hLeftSeg₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ (free+2*q) (_root_.ThreeSum.CyclicFold.padTo q (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))) := by
    intro i hi
    have hlen : (_root_.ThreeSum.CyclicFold.padTo q (_root_.ThreeSum.CyclicFold.vector p (fun z => H (-z)))).length = q :=
      _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.padTo_length _ _ (by rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega,Or.inr (by omega)⟩]
    exact hLeftSeg i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free) (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba F H hw hpq hRightSeg hLeftSeg₂ hFbound hHbound (by change free + q + q ≤ free + 5 * q + N; omega) (by change free + 2 * q + q ≤ free + 5 * q + N; omega) (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega) (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega) hkw (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.meets (d := d + 1) (k := Nat.clog 2 p) (a := free + q) (b := free + 2 * q) (prod := free + 3 * q) (dst := free) (work := free + 5 * q + N) C.offset C.cyclic C.minimum C.karatsuba F H hw hpq hRightSeg hLeftSeg₂ hFbound hHbound (by change free + q + q ≤ free + 5 * q + N; omega) (by change free + 2 * q + q ≤ free + 5 * q + N; omega) (by change free + 3 * q + 2 * q ≤ free + 5 * q + N; omega) (by omega) (by right; change free + p ≤ free + 3 * q; omega) (by change free + 5 * q + N + 8 * q ≤ lim.space; omega) hkw (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, q, _root_.ThreeSum.KaratsubaInterface.capacity]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [q, _root_.ThreeSum.KaratsubaInterface.capacity] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, q, _root_.ThreeSum.KaratsubaInterface.capacity] <;> omega)
     on_goal -1 => (rintro result μ₃ ⟨hresult, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hresult,?_⟩
  intro i hi
  change μ₃ i = μ i
  rw [hkeep₃ i (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  exact (hkeep₂ i ⟨by omega,Or.inl (by omega)⟩).trans
    (hkeep₁ i ⟨by omega,Or.inl (by omega)⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets__implementation_cb7e924924) := (@ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.Procs.meets__implementation_cb7e924924)

#print axioms solution
