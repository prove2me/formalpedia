-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:13:44.341111+00:00
-- url     : https://prove2.me/submissions/debc7348-4b3e-424c-8c84-3811a45bf0f5

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightClassFilter_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorArray_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
namespace ThreeSum.LightColorClasses
end ThreeSum.LightColorClasses
namespace ThreeSum.LightColorIndex
end ThreeSum.LightColorIndex
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ColorClassLists
end ThreeSum1960614.Machine.ThreeSum.ColorClassLists
namespace ThreeSum1960614.Machine.ThreeSum.LightClassFilter
end ThreeSum1960614.Machine.ThreeSum.LightClassFilter
namespace ThreeSum1960614.Machine.ThreeSum.LightColorClasses
end ThreeSum1960614.Machine.ThreeSum.LightColorClasses
namespace ThreeSum1960614.Machine.ThreeSum.LightColorIndex
end ThreeSum1960614.Machine.ThreeSum.LightColorIndex
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter
open _root_.ThreeSum.LightClassFilter


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000







theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (_root_.ThreeSum.LightClassFilter.items x color want scale n).length ≤ n := by
  simpa only [_root_.ThreeSum.LightClassFilter.items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}







end ThreeSum.LightClassFilter

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual evaluation of one member of the deterministic coloring family

Two calls to the checked mask-coordinate routine inspect the selected bits
of an original array index. Four literal color arguments determine the map
from bit patterns to the three colors. The cost is linear in the binary
width and independent of the numeric index magnitude.
-/

namespace ThreeSum.LightColorIndex
open _root_.ThreeSum.LightColorIndex


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem color_lt {W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (m : ℕ) : _root_.ThreeSum.LightColorIndex.color p m < 3 :=
  (p.2 _).isLt













end ThreeSum.LightColorIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists
open _root_.ThreeSum.ColorClassLists


open _root_.ThreeSum.LightClassFilter
open _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter



@[simp] theorem value_fin {n : ℕ} (x : Fin n → ℤ) (i : Fin n) : _root_.ThreeSum.ColorClassLists.value x i.val = x i := by
  simp [_root_.ThreeSum.ColorClassLists.value,i.isLt]









theorem length_classList_le {n W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (_root_.ThreeSum.ColorClassLists.classList p x c scale).length ≤ n :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.items_length_le ..













end ThreeSum.ColorClassLists

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorClasses
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorClasses

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorClassLists
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs.meets__implementation_6728f4c033 {pMain src n W colors dst0 dst1 dst2 work U : ℕ} {μ : ℕ → ℤ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs P pMain) (p : _root_.ThreeSum.Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+(n+1) ≤ dst1) (h1 : dst1+(n+1) ≤ dst2) (h2 : dst2+(n+1) ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hU : (U : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) (hread : _root_.ThreeSum1960614.Machine.Light.Seg μ src (List.ofFn x))
    (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,work] μ (_root_.ThreeSum.LightColorClasses.time W n)
      (fun _ ν => _root_.ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Output p x μ ν colors dst0 dst1 dst2) := by
  have hW := p.1.1.isLt
  have h3 : (3 : ℤ) ≤ lim.word := by
    have hh : 2^2 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hh' : (4 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hh
    omega
  have read : ∀ i < n, μ (src+i) = _root_.ThreeSum.ColorClassLists.value x i := by
    intro i hi
    have hh := hread i (by simpa using hi)
    simpa only [List.getElem_ofFn,← _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.value_fin x ⟨i,hi⟩] using hh
  have bound : ∀ i < n, |_root_.ThreeSum.ColorClassLists.value x i| ≤ (U : ℤ) := by
    intro i hi
    simpa only [_root_.ThreeSum.ColorClassLists.value,hi,dite_true] using hbound ⟨i,hi⟩
  have len0 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 0 1
  have len1 := _root_.ThreeSum1960614.Machine.ThreeSum.ColorClassLists.length_classList_le p x 1 1
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightColorClasses.body _root_.ThreeSum.LightColorClasses.time
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorArray.meets (d := d+1) (n := n) (dst := colors) (work := work)
    C.colors C.powers C.color C.erase μ p hw hn (by omega) hspace hword (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨color₁, _, keep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have read₁ : ∀ i < n, ν₁ (src+i) = _root_.ThreeSum.ColorClassLists.value x i := by
    intro i hi
    exact (keep₁ _ ⟨by omega,Or.inl (by omega)⟩).trans (read i hi)
  have hf0 := _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.meets (d := d+1) (μ := ν₁) (src := src) (colors := colors)
    (dst := dst0) (n := n) (want := 0) (scale := 1) (U := U) C.filter
    (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) hw h3 (by omega) hcolors (by omega)
    (by decide) (by norm_num) hU read₁ color₁ (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightColorIndex.color_lt p i) bound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf0 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf0 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨_, header0, values0, keep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have read₂ : ∀ i < n, ν₂ (src+i) = _root_.ThreeSum.ColorClassLists.value x i := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (read₁ i hi)
  have color₂ : ∀ i < n, ν₂ (colors+i) = (_root_.ThreeSum.LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₂ _ (Or.inl (by omega))).trans (color₁ i hi)
  have hf1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.meets (d := d+1) (μ := ν₂) (src := src) (colors := colors)
    (dst := dst1) (n := n) (want := 1) (scale := 1) (U := U) C.filter
    (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₂ color₂ (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightColorIndex.color_lt p i) bound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf1 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf1 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro r ν₃ ⟨_, header1, values1, keep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have read₃ : ∀ i < n, ν₃ (src+i) = _root_.ThreeSum.ColorClassLists.value x i := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (read₂ i hi)
  have color₃ : ∀ i < n, ν₃ (colors+i) = (_root_.ThreeSum.LightColorIndex.color p i : ℤ) := by
    intro i hi
    exact (keep₃ _ (Or.inl (by omega))).trans (color₂ i hi)
  have hf2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightClassFilter.meets (d := d+1) (μ := ν₃) (src := src) (colors := colors)
    (dst := dst2) (n := n) (want := 2) (scale := -1) (U := U) C.filter
    (_root_.ThreeSum.ColorClassLists.value x) (_root_.ThreeSum.LightColorIndex.color p) hw h3 (by omega) (by omega) (by omega)
    (by decide) (by norm_num) hU read₃ color₃ (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightColorIndex.color_lt p i) bound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf2 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf2 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorArray.time, _root_.ThreeSum.LightColorIndex.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightClassFilter.time] <;> omega)
     on_goal -1 => (rintro r ν₄ ⟨_, header2, values2, keep₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,?_,?_,?_,?_,header2,values2,?_⟩
  · intro i hi
    exact (keep₄ _ (Or.inl (by omega))).trans (color₃ i hi)
  · exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans header0)
  · exact (values0.of_sameOutside keep₃ (Or.inl (by change dst0+1+(_root_.ThreeSum.ColorClassLists.classList p x 0 1).length ≤ dst1; omega))).of_sameOutside
      keep₄ (Or.inl (by change dst0+1+(_root_.ThreeSum.ColorClassLists.classList p x 0 1).length ≤ dst2; omega))
  · exact (keep₄ _ (Or.inl (by omega))).trans header1
  · exact values1.of_sameOutside keep₄ (Or.inl (by change dst1+1+(_root_.ThreeSum.ColorClassLists.classList p x 1 1).length ≤ dst2; omega))
  · intro a ha
    exact (keep₄ _ (Or.inl (by omega))).trans
      ((keep₃ _ (Or.inl (by omega))).trans
        ((keep₂ _ (Or.inl (by omega))).trans (keep₁ _ ⟨by omega,Or.inl ha⟩)))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs.meets__implementation_6728f4c033) := (@ThreeSum1960614.Machine.ThreeSum.LightColorClasses.Procs.meets__implementation_6728f4c033)

#print axioms solution
