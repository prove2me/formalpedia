-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:40:52.034404+00:00
-- url     : https://prove2.me/submissions/afa38b6e-3689-4249-a2e0-a9c63a7b7ea9

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightResidues_residues_ends

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
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues

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













theorem residues_meets {pResidues pEmod : ℕ}
    (hres : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {src dst n p work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hsrc : src + n ≤ work) (hdst : dst + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst n) (hc : |c| ≤ 1)
    (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pResidues d [src, dst, n, p, work, c] μ (_root_.ThreeSum.LightResidues.residuesTime n U)
      fun _ μ' =>
        (∀ i < n, μ' (dst + i) = (_root_.ThreeSum.LightResidues.residue p c (μ (src + i)) : ℤ)) ∧
          _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst n := by
  exact _root_.ThreeSum1960614.Machine.Light.Meets.of_body hres (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residues_ends hem hw hd hp hsrc hdst hspace hsep hc hword hvalues)

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



theorem padded_histogram_segment {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) {n cap dst : ℕ} {μ : ℕ → ℤ}
    (hcap : p ≤ cap)
    (hout : ∀ r < cap, μ (dst + r) =
      (_root_.ThreeSum.LightHistogram.count (fun i => _root_.ThreeSum.LightResidues.residue p c (values i)) r n : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum.CyclicFold.padTo cap (_root_.ThreeSum.CyclicFold.vector p (_root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n))) := by
  intro r hr
  have hlen : (_root_.ThreeSum.CyclicFold.padTo cap (_root_.ThreeSum.CyclicFold.vector p (_root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n))).length = cap := by
    apply _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.padTo_length
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold.vector_length]
    exact hcap
  have hrcap : r < cap := by omega
  rw [← List.getD_eq_getElem _ 0 hr, _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.padded_histogram_getD]
  exact hout r hrcap













end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram

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
section

theorem ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets__implementation_6c70d64be2 {pMain pResidues pEmod pHistogram pFill : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residuesBody pEmod))
    (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    (hhist : P[pHistogram]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill))
    (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 0 < p) (hcap : p ≤ cap)
    (hsrc : src + n ≤ codes) (hdst : dst + cap ≤ codes)
    (hcodes : codes + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src, dst, n, p, cap, codes, work, c] μ (_root_.ThreeSum.LightResidueHistogram.time n cap U)
      fun _ μ' =>
        _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum.CyclicFold.padTo cap (_root_.ThreeSum.CyclicFold.vector p (_root_.ThreeSum.LightResidueHistogram.signedHistogram p c (fun i => μ (src+i)) n))) ∧
          _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' codes dst cap := by
  haveI : NeZero p := ⟨hp.ne'⟩
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.body _root_.ThreeSum.LightResidueHistogram.time
  have hcall := _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residues_meets (d := d + 1) (src := src) (dst := codes)
    (n := n) (p := p) (work := work) (c := c) hres hem hw hd hp
    (by omega) hcodes hspace (by left; omega) hc hword hvalues
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨hkeys, hkept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hcall₂ := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets (d := d + 1) (src := codes) (dst := dst)
    (n := n) (p := cap) (μ := μ₁) hhist hfill
    (fun i => _root_.ThreeSum.LightResidues.residue p c (μ (src + i))) hw hd
    (by omega) (by omega) (by right; omega) hkeys
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp c (μ (src + i))).trans_le hcap)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall₂ _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall₂ ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightResidues.residuesTime, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightResidues.residueBudget] <;> omega)
     on_goal -1 => (rintro _ μ₂ ⟨hcounts, hkept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.padded_histogram_segment c (fun i => μ (src + i)) hcap hcounts, ?_⟩
  intro a ⟨ha, hout⟩
  exact (hkept₂ a hout).trans (hkept₁ a ⟨by omega, by omega⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets__implementation_6c70d64be2) := (@ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.meets__implementation_6c70d64be2)

#print axioms solution
