-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:40.265107+00:00
-- url     : https://prove2.me/submissions/a62fe677-cdca-46e2-87d2-beafb0ebd2f2

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
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
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandPartition_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightBandPartition
end ThreeSum.LightBandPartition
namespace ThreeSum.LightSmallDivide
end ThreeSum.LightSmallDivide
namespace ThreeSum.LightSortedBands
end ThreeSum.LightSortedBands
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPartition
end ThreeSum1960614.Machine.ThreeSum.LightBandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
end ThreeSum1960614.Machine.ThreeSum.LightSmallDivide
namespace ThreeSum1960614.Machine.ThreeSum.LightSortedBands
end ThreeSum1960614.Machine.ThreeSum.LightSortedBands
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

























end ThreeSum.BandPartition

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

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





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

































































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide
open _root_.ThreeSum.LightSmallDivide


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











theorem time_bound (a b : ℕ) : _root_.ThreeSum.LightSmallDivide.time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold _root_.ThreeSum.LightSmallDivide.time
  omega

end ThreeSum.LightSmallDivide

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing consecutive band endpoints in actual memory

The program computes the number of bands itself. Its quotient loop is charged
linearly in that number, and both endpoint passes issue bounded-address
loads from the sorted source. Output arrays reserve `n` cells each; only the
computed band count is populated.
-/

namespace ThreeSum.LightBandPartition
open _root_.ThreeSum.LightBandPartition


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}























theorem time_bound (n g : ℕ) : _root_.ThreeSum.LightBandPartition.time n g ≤ 200*n+200 := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g
  have hdiv := _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.time_bound (n-1) g
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold _root_.ThreeSum.LightBandPartition.time _root_.ThreeSum.LightBandPartition.lowerTime _root_.ThreeSum.LightBandPartition.upperTime
  omega

end ThreeSum.LightBandPartition

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSortedBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets__implementation_fd33c354eb {pMain src values endpoints work g d : ℕ}
    {μ : ℕ → ℤ} {original : List ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+original.length ≤ values) (hvalues : values+original.length ≤ endpoints)
    (hendpoints : endpoints+2+2*original.length ≤ work)
    (hspace : _root_.ThreeSum.LightSortedBands.space work original.length ≤ lim.space)
    (hword : ((original.length+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hd : d+original.length+Nat.clog 2 original.length+3 ≤ lim.depth)
    (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src original) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,original.length,g,values,endpoints,work] μ (_root_.ThreeSum.LightSortedBands.time original.length)
      (fun r μ' => r = μ' (endpoints+1) ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ' values endpoints g original ∧
        ∀ a, a < work → (a < src ∨ src+original.length ≤ a) →
          (a < values ∨ values+original.length ≤ a) →
          (a < endpoints ∨ endpoints+2+2*original.length ≤ a) → μ' a = μ a) := by
  have h1 : (1 : ℤ) ≤ lim.word := by omega
  have hspace' : work+original.length ≤ lim.space := hspace
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.body _root_.ThreeSum.LightSortedBands.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.normalize.meets (d := d + 1) (src := src) (dst := values) (work := work) hw h1 hread hsrc (by omega) hspace (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.normalize.meets (d := d + 1) (src := src) (dst := values) (work := work) hw h1 hread hsrc (by omega) hspace (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;> omega)
     on_goal -1 => (rintro len μ₁ ⟨L, hlen, hL, hstrict, hcount, hmem, hkept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hLread : ∀ i < L.length, μ₁ (values+i) = L.getD i 0 := by
    intro i hi
    exact hL.getD hi 0
  have hpart := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.meets (d := d+1) (src := values) (dst := endpoints+2)
    R.partition R.divide R.lower R.upper μ₁ (fun i => L.getD i 0) hw hg
    (by omega) (by unfold _root_.ThreeSum.LightSortedBands.space at hspace; omega)
    ((Int.ofNat_le.mpr (by omega : L.length+g+2 ≤ original.length+g+2)).trans hword)
    hLread (by omega)
  have hpartTime : _root_.ThreeSum.LightBandPartition.time L.length g ≤ 200*original.length+200 :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPartition.time_bound _ _).trans (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hpart.mono_time hpartTime) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpart.mono_time hpartTime) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;> omega)
     on_goal -1 => (rintro bands μ₂ ⟨hbands, hlo, hhi, hkept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hL₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ values L := by
    intro i hi
    rw [hkept₂ (values+i) (Or.inl (by omega))]
    exact hL i hi
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen endpoints (L.length : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (endpoints + 1) (_root_.ThreeSum.BandPartition.size L.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size L.length g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbands, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightSortedBands.space] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,⟨L,?_,hstrict,hcount,hmem,?_,?_,?_,?_⟩,?_⟩
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (_root_.ThreeSum.BandPartition.size L.length g : ℤ) (values+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hL₂ i hi
  · simp
  · simp
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (_root_.ThreeSum.BandPartition.size L.length g : ℤ) (endpoints+2+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hlo i hi
  · intro i hi
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (_root_.ThreeSum.BandPartition.size L.length g : ℤ) (endpoints+2+L.length+i) = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hhi i hi
  · intro a ha hsrc hvalues hendpoints
    change Function.update (Function.update μ₂ endpoints (L.length : ℤ)) (endpoints+1)
      (_root_.ThreeSum.BandPartition.size L.length g : ℤ) a = _
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),hkept₂ a (by omega)]
    exact hkept₁ a ha hsrc hvalues
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets__implementation_fd33c354eb) := (@ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Procs.meets__implementation_fd33c354eb)

#print axioms solution
