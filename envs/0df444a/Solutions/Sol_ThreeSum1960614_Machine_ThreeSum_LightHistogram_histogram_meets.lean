-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:27:39.018055+00:00
-- url     : https://prove2.me/submissions/cf5a3429-ce32-4a4e-aa15-82cbdb24c276

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_count_ends

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Copy
end Light.Copy
namespace Light.Fill
end Light.Fill
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram

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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}













/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : _root_.Light.wrote μ dst f j (dst + i) = f i := by
  unfold _root_.Light.wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]









/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : _root_.ThreeSum1960614.Machine.Light.Seg (_root_.Light.wrote μ dst f n) dst l := fun i hi => by
  rw [_root_.ThreeSum1960614.Machine.Light.wrote_done (hl ▸ hi), h i hi]





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## copy -/

namespace Copy
open _root_.Light.Copy







end Copy







/-! ## fill -/

namespace Fill
open _root_.Light.Fill







end Fill





/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), n, x] μ (_root_.Light.fillTime n) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (List.replicate n x) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n :=
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun _ => x) (fun i hi => by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                                                                                                        (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                                                                                                        simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    ⟨_root_.ThreeSum1960614.Machine.Light.seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
                                                                                                                       intro p2m_macro_6937110504482591170 p2m_macro_1179512947086756631
                                                                                                                       first
                                                                                                                       | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_17476295892461720639); (try have := p2m_macro_17476295892461720639 p2m_macro_6937110504482591170 (by omega)); revert p2m_macro_17476295892461720639)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       |
                                                                                                                         (simp [] at p2m_macro_1179512947086756631;
                                                                                                                           ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_2569603476276785208); (try have := p2m_macro_2569603476276785208 p2m_macro_6937110504482591170 (by omega)); revert p2m_macro_2569603476276785208)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_2840815898746619592); (try have := p2m_macro_2840815898746619592 p2m_macro_6937110504482591170 (by omega)); revert p2m_macro_2840815898746619592)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                                                                                                                           fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                                                       its condition K x does not follow from the hypotheses.")))⟩
    hw hdst rfl rfl (hT := by (first
                               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.fillTime]
                                   first
                                   | omega
                                   | (ring_nf; omega))
                               | omega
                               |
                                 (simp [_root_.Light.fillTime] <;>
                                     first
                                     | omega
                                     | (ring_nf; omega)))))

end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

/-- Actual clearing, incrementing, and memory-preservation contract. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets__implementation_9def5d8699 {pHist pFill : ℕ}
    (hp : P[pHist]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody pFill))
    (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdepth : d < lim.depth)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : _root_.Light.Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pHist d [(src : ℤ), dst, n, p] μ (_root_.ThreeSum.LightHistogram.histogramTime n p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = _root_.ThreeSum.LightHistogram.count key r n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogramBody _root_.ThreeSum.LightHistogram.histogramTime
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.fill_meets hfill (μ := μ) (x := 0) hw hD) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.fill_meets hfill (μ := μ) (x := 0) hw hD) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro res μ₁ ⟨hfilled, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hread : ∀ i < n, μ₁ (src + i) = key i := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hzero : ∀ r < p, μ₁ (dst + r) = 0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_ends key (by simp) (by simp) (by simp)
    hw hS hD hsep hread hkeyLt hzero)
  · intro σ' hpost
    exact ⟨hpost.1, fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets__implementation_9def5d8699) := (@ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets__implementation_9def5d8699)

#print axioms solution
