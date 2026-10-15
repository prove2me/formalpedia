-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:14.06655+00:00
-- url     : https://prove2.me/submissions/09106277-3afa-49e9-adde-a443008e4b33

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryWeights_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedEnumeration_meets
import Theorems.Thm_ThreeSum_QueryCoordinates_output_missingSets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightQueryEnumeration
end ThreeSum.LightQueryEnumeration
namespace ThreeSum.LightQueryWeights
end ThreeSum.LightQueryWeights
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
end ThreeSum1960614.Machine.ThreeSum.LightQueryWeights
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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



















































/-- Reading a cell of a segment of natural numbers. -/
theorem SegN.read {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = ((l.getD i 0 : ℕ) : ℤ) := by
  rw [h i (by simpa using hi), List.getElem_map, List.getD_eq_getElem _ _ hi]



























end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



@[simp] theorem selectedPowers_length {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.selectedPowers Q j).length = (_root_.ThreeSum.QueryCoordinates.positions Q j).length := by simp [_root_.ThreeSum.QueryCoordinates.selectedPowers]





@[simp] theorem selectedPowers_sum {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.selectedPowers Q W).sum = _root_.ThreeSum.SubsetAddress.subsetMask Q := by
  rw [_root_.ThreeSum.QueryCoordinates.selectedPowers,← List.sum_toFinset _ (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset]
  rfl



theorem total_getD (xs : List ℕ) :
    _root_.ThreeSum.LightWeightedEnumeration.total (fun i => xs[i]?.getD 0) xs.length = xs.sum := by
  unfold _root_.ThreeSum.LightWeightedEnumeration.total
  rw [← Fin.sum_univ_eq_sum_range]
  simpa using Fin.sum_univ_getElem xs

@[simp] theorem total_weights {W : ℕ} (Q : Finset (Fin W)) :
    _root_.ThreeSum.LightWeightedEnumeration.total (_root_.ThreeSum.QueryCoordinates.weights Q) Q.card = _root_.ThreeSum.SubsetAddress.subsetMask Q := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.positions_length Q,← _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.selectedPowers_length Q W]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.total_getD (_root_.ThreeSum.QueryCoordinates.selectedPowers Q W)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.selectedPowers_sum Q)































end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights
open _root_.ThreeSum.LightQueryWeights


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem weights_of_segment {μ : ℕ → ℤ} {W dst : ℕ} {Q : Finset (Fin W)}
    (hseg : _root_.ThreeSum1960614.Machine.Light.SegN μ dst (_root_.ThreeSum.QueryCoordinates.selectedPowers Q W)) :
    _root_.ThreeSum.LightWeightedEnumeration.Weights μ dst Q.card (_root_.ThreeSum.QueryCoordinates.weights Q) := by
  intro i hi
  have hi' : i < (_root_.ThreeSum.QueryCoordinates.selectedPowers Q W).length := by simpa using hi
  simpa only [_root_.ThreeSum.QueryCoordinates.weights,List.getD_eq_getElem _ _ hi',List.getElem?_eq_getElem hi',Option.getD_some]
    using hseg.read hi'



end ThreeSum.LightQueryWeights

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightQueryEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets__implementation_d5be199829 {pMain pWeights pPowers pErase pEnum : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body pWeights pEnum))
    (hweights : P[pWeights]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.body pPowers pErase))
    (hpowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (herase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {W t dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,dst,work] μ (_root_.ThreeSum.LightQueryEnumeration.time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst ((_root_.ThreeSum.QueryCoordinates.missingSets Q t).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum.LightWeightedEnumeration.Weights μ' work Q.card (_root_.ThreeSum.QueryCoordinates.weights Q) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst (Q.card.choose t)) := by
  have hc : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hm : (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.SubsetAddress.subsetMask Q ≤ 2^(W+1) :=
      (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask Q).1).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (subsetMask Q : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.body _root_.ThreeSum.LightQueryEnumeration.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (work + W + 1 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hbuild := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.meets (d := d+1) (μ := μ)
    (dst := work) (work := work+W+1) hweights hpowers herase Q
    hw (by omega) (by omega) hword (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hbuild _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hbuild ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time] <;> omega)
     on_goal -1 => (rintro count μ₁ ⟨hcount, hseg, _, hkept₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hwtable := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryWeights.weights_of_segment hseg
  have henumCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedEnumeration.meets (W := Q.card) (U := _root_.ThreeSum.SubsetAddress.subsetMask Q)
    henum hw (by omega) hm Q.card t 0 dst μ₁ le_rfl ht
    (by simp) hdst hwtable (d+1) (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (henumCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen henumCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time, hcount]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time, hcount] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryWeights.time, _root_.ThreeSum.LightSubsetEnumeration.time, hcount] <;> omega)
     on_goal -1 => (rintro res μ₂ ⟨hres, hout, hkept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨by simpa using hres,?_,?_,?_⟩
  · simpa only [_root_.ThreeSum.QueryCoordinates.output_missingSets] using hout
  · intro i hi
    change μ₂ (work+i) = _
    rw [hkept₁ (work+i) (Or.inr (by omega))]
    exact hwtable i hi
  · intro i hi
    exact (hkept₁ i hi.2).trans (hkept₀ i ⟨by omega,Or.inl hi.1⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets__implementation_d5be199829) := (@ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets__implementation_d5be199829)

#print axioms solution
