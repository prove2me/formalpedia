-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:07:27.619637+00:00
-- url     : https://prove2.me/submissions/fdc7454f-2df9-44cd-8e08-93bd045995da

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverScores_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverUpdate_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMinimum_meets
import Theorems.Thm_ThreeSum_BooleanGreedy_active_succ
import Theorems.Thm_ThreeSum_BooleanGreedy_choice_eq_least

private theorem platform_seg_cons_378c7cef36 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_378c7cef36 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_378c7cef36 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


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
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSum.Cover
end ThreeSum.Cover
namespace ThreeSum.LightCoverGreedy
end ThreeSum.LightCoverGreedy
namespace ThreeSum.LightCoverSelect
end ThreeSum.LightCoverSelect
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
end ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
namespace ThreeSum1960614.Machine.ThreeSum.Cover
end ThreeSum1960614.Machine.ThreeSum.Cover
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy
end ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverSelect
end ThreeSum1960614.Machine.ThreeSum.LightCoverSelect
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover
open _root_.ThreeSum.Cover


open _root_.Finset
open scoped _root_.BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]



theorem selectMap_mem (maps : List Ω) (hne : maps ≠ [])
    (covers : Ω → U → Prop) [DecidableRel covers] (targets : Finset U) :
    _root_.ThreeSum.Cover.selectMap maps covers targets ∈ maps := by
  unfold _root_.ThreeSum.Cover.selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => exact False.elim (hne (List.argmax_eq_none.mp h))
  | some ω =>
    simp only [Option.getD_some]
    exact List.argmax_mem (f := fun ω => (targets.filter (covers ω)).card)
      (by simpa only [Option.mem_def] using h)























end ThreeSum.Cover

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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (x : ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  platform_seg_append_378c7cef36.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [platform_seg_cons_378c7cef36]⟩





/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a' n' := fun b hb => h b (by omega)

/-- Writing inside the region. -/
theorem SameOutside.update (h : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc





/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)































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
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun _ => x) (fun i hi => by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    ⟨_root_.ThreeSum1960614.Machine.Light.seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by 
        (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
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

namespace ThreeSum1960614.Machine

/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy
open _root_.ThreeSum.BooleanGreedy


open _root_.Finset
open scoped _root_.BigOperators















theorem active_le (matrix : ℕ → ℕ → ℕ) (rows cols t j : ℕ) :
    _root_.ThreeSum.BooleanGreedy.active matrix rows cols t j ≤ 1 := by unfold _root_.ThreeSum.BooleanGreedy.active; split <;> omega

theorem active_zero {matrix : ℕ → ℕ → ℕ} {rows cols j : ℕ} (hj : j < cols) :
    _root_.ThreeSum.BooleanGreedy.active matrix rows cols 0 j = 1 := by simp [_root_.ThreeSum.BooleanGreedy.active,_root_.ThreeSum.BooleanGreedy.state,_root_.ThreeSum.Cover.greedyState,hj]



theorem choice_lt {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ} (hrows : 0 < rows) (t : ℕ) :
    _root_.ThreeSum.BooleanGreedy.choice matrix rows cols t < rows := by
  apply List.mem_range.mp
  exact _root_.ThreeSum1960614.Machine.ThreeSum.Cover.selectMap_mem _ (by simpa using hrows.ne') _ _





theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (_root_.ThreeSum.BooleanGreedy.choices matrix rows cols t).length = t := _root_.ThreeSum.Cover.greedyChoices_length ..

theorem choices_succ (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    _root_.ThreeSum.BooleanGreedy.choices matrix rows cols (t+1) = _root_.ThreeSum.BooleanGreedy.choices matrix rows cols t ++ [_root_.ThreeSum.BooleanGreedy.choice matrix rows cols t] := rfl

end ThreeSum.BooleanGreedy

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual first-maximum candidate selection from a Boolean cover matrix -/

namespace ThreeSum.LightCoverSelect
open _root_.ThreeSum.LightCoverSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem meets {pMain pScores pDot pMinimum : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverSelect.body pScores pMinimum))
    (hscores : P[pScores]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverScores.body pDot))
    (hdot : P[pDot]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body)
    (hminimum : P[pMinimum]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.body)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,activePtr,work,rows,cols] μ (_root_.ThreeSum.LightCoverSelect.time rows cols)
      (fun r μ' =>
        r = (_root_.ThreeSum.LightMinimum.least (fun i => -(_root_.ThreeSum.LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' work rows) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverSelect.body _root_.ThreeSum.LightCoverSelect.time
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverScores.meets (d := d+1) (μ := μ)
    (src := src) (activePtr := activePtr) (dst := work) (rows := rows) (cols := cols)
    hscores hdot matrix active hw hd hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time] <;> omega)
     on_goal -1 => (rintro v μ₁ ⟨written, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.meets (d := d+1) (μ := μ₁) (src := work) (n := rows)
    hminimum (fun i => -(_root_.ThreeSum.LightCoverScores.score matrix active cols i : ℤ))
    hw hrows hspace written
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightMinimum.time] <;> omega)
     on_goal -1 => (rintro r μ₂ ⟨hr, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  exact ⟨hr,kept⟩



theorem Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverSelect.Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr work rows cols : ℕ}
    (matrix : ℕ → ℕ → ℕ) (active : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ work) (hactive : activePtr+cols ≤ work)
    (hspace : work+rows ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hreadActive : ∀ j < cols, μ (activePtr+j) = (active j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hactiveValue : ∀ j < cols, active j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,activePtr,work,rows,cols] μ (_root_.ThreeSum.LightCoverSelect.time rows cols)
      (fun r μ' =>
        r = (_root_.ThreeSum.LightMinimum.least (fun i => -(_root_.ThreeSum.LightCoverScores.score matrix active cols i : ℤ)) rows : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' work rows) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverSelect.meets S.main S.scores S.dot S.minimum matrix active hw hd hrows
    hsrc hactive hspace hread hreadActive hmatrix hactiveValue hword





end ThreeSum.LightCoverSelect

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCoverGreedy
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BooleanGreedy
open _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
set_option maxHeartbeats 1200000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets__implementation_46d0bbee34 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs P pMain)
    {μ : ℕ → ℤ} {src activePtr rows cols rounds : ℕ}
    (matrix : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hrows : 0 < rows)
    (hsrc : src+rows*cols ≤ activePtr)
    (hspace : activePtr+_root_.ThreeSum.LightCoverGreedy.total rows cols rounds ≤ lim.space)
    (hread : ∀ i < rows, ∀ j < cols, μ (src+i*cols+j) = (matrix i j : ℤ))
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,activePtr,rows,cols,rounds] μ (_root_.ThreeSum.LightCoverGreedy.time rows cols rounds)
      (fun r μ' => r = (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg μ' (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols) ((_root_.ThreeSum.BooleanGreedy.choices matrix rows cols rounds).map (fun x : ℕ => (x : ℤ))) ∧
        (∀ j < cols, μ' (activePtr+j) = (_root_.ThreeSum.BooleanGreedy.active matrix rows cols rounds j : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' activePtr (_root_.ThreeSum.LightCoverGreedy.total rows cols rounds)) := by
  have hspace' : activePtr+cols+rows+rounds ≤ lim.space := by simpa [_root_.ThreeSum.LightCoverGreedy.total,Nat.add_assoc] using hspace
  have hworkSpace : activePtr+cols+rows ≤ lim.space := by omega
  have hactiveSpace : activePtr+cols ≤ lim.space := by omega
  have houtSpace : _root_.ThreeSum.LightCoverGreedy.out activePtr rows cols+rounds ≤ lim.space := by simpa [_root_.ThreeSum.LightCoverGreedy.out] using hspace'
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.body _root_.ThreeSum.LightCoverGreedy.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (activePtr + cols : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols) (x := 1) S.fill hw hactiveSpace) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := μ) (dst := activePtr) (n := cols) (x := 1) S.fill hw hactiveSpace) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;> omega)
     on_goal -1 => (rintro vf μ₁ ⟨hfill, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (T := rounds*(_root_.ThreeSum.LightCoverGreedy.roundTime rows cols+8)+6)
    (Q := fun σ => _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Inv μ matrix src activePtr rows cols rounds rounds σ)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Inv μ matrix src activePtr rows cols rounds) rounds (_root_.ThreeSum.LightCoverGreedy.roundTime rows cols)
    ?_ ?_ ?_ ?_ (hT := by (first
                           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.roundTime]
                               first
                               | omega
                               | (ring_nf; omega))
                           | omega
                           |
                             (simp [_root_.ThreeSum.LightCoverGreedy.roundTime] <;>
                                 first
                                 | omega
                                 | (ring_nf; omega))))) ?_
  · refine ⟨0,vf,μ₁,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Inv,_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal,_root_.ThreeSum.LightCoverGreedy.out]
    · intro j hj
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.active_zero hj]
      exact (hfill j (by simpa using hj)).trans (List.getElem_replicate ..)
    · simp [_root_.ThreeSum.BooleanGreedy.choices,_root_.ThreeSum.Cover.greedyChoices]
    · exact hkept.mono le_rfl (by unfold _root_.ThreeSum.LightCoverGreedy.total; omega)
  · rintro i _ hi _ ⟨r,v,μ',rfl,hactive,written,kept⟩
    have hmread : ∀ a < rows, ∀ j < cols, μ' (src+a*cols+j) = (matrix a j : ℤ) := by
      intro a ha j hj
      have hm : (a+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
      have haddr : src+a*cols+j < activePtr := by nlinarith
      rw [kept _ (Or.inl haddr)]
      exact hread a ha j hj
    have hchoice := _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choice_lt (matrix := matrix) (cols := cols) hrows i
    have hcWord : (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℤ) ≤ lim.word := by
      have hh : _root_.ThreeSum.BooleanGreedy.choice matrix rows cols i ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.roundBody
    have hs := S.select.meets (d := d+1) (μ := μ')
      (src := src) (activePtr := activePtr) (work := activePtr+cols) (rows := rows) (cols := cols)
      matrix (_root_.ThreeSum.BooleanGreedy.active matrix rows cols i) hw (by omega) hrows (by omega) le_rfl
      hworkSpace hmread hactive hmatrix (fun j _ => _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.active_le matrix rows cols i j) hword
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;> omega)
       on_goal -1 => (rintro selected μ₂ ⟨hselected, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hselected' : selected = (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℤ) := by
      rw [hselected,_root_.ThreeSum.BooleanGreedy.choice_eq_least hrows hmatrix i]
    have hactive₂ : ∀ j < cols, μ₂ (activePtr+j) = (_root_.ThreeSum.BooleanGreedy.active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [hkeep₂ _ (Or.inl (by omega))]
      exact hactive j hj
    have hwritten₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols)
        ((_root_.ThreeSum.BooleanGreedy.choices matrix rows cols i).map (fun x : ℕ => (x : ℤ))) :=
      written.of_sameOutside hkeep₂ (Or.inr (by unfold _root_.ThreeSum.LightCoverGreedy.out; omega))
    have hkeep₂full : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ₂ activePtr (_root_.ThreeSum.LightCoverGreedy.total rows cols rounds) := by
      intro a ha
      rw [hkeep₂ _ (by unfold _root_.ThreeSum.LightCoverGreedy.total at ha; omega)]
      exact kept a ha
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols + i) (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselected', _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hselected', _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselected', _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    let μ₃ := Function.update μ₂ (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols+i) (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℤ)
    have hchoices₃ : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols)
        ((_root_.ThreeSum.BooleanGreedy.choices matrix rows cols (i+1)).map (fun x : ℕ => (x : ℤ))) := by
      have hh := hwritten₂.snoc (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℤ)
      simpa [_root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_succ,List.map_append,List.map_singleton,_root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_length,μ₃] using hh
    have hactive₃ : ∀ j < cols, μ₃ (activePtr+j) = (_root_.ThreeSum.BooleanGreedy.active matrix rows cols i j : ℤ) := by
      intro j hj
      rw [show μ₃ (activePtr+j) = μ₂ (activePtr+j) by
        unfold μ₃; rw [Function.update_of_ne (by unfold _root_.ThreeSum.LightCoverGreedy.out; omega)]]
      exact hactive₂ j hj
    have hkeep₃ : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ₃ activePtr (_root_.ThreeSum.LightCoverGreedy.total rows cols rounds) :=
      hkeep₂full.update ⟨by unfold _root_.ThreeSum.LightCoverGreedy.out; omega,by unfold _root_.ThreeSum.LightCoverGreedy.out _root_.ThreeSum.LightCoverGreedy.total; omega⟩ _
    have hmul : (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i+1)*cols ≤ rows*cols := Nat.mul_le_mul_right cols (by omega)
    have hrow : src+_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols+cols ≤ activePtr := by nlinarith
    have hrowSpace : src+_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols+cols ≤ lim.space := by omega
    have hrowRead : ∀ j < cols,
        μ₃ (src+_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols+j) = (matrix (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i) j : ℤ) := by
      intro j hj
      rw [hkeep₃ _ (Or.inl (by omega))]
      exact hread _ hchoice j hj
    have hmulWord : ((_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols : ℕ) : ℤ) ≤ lim.word := by
      have hh : _root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have haddr : ((src : ℤ)+(_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i : ℤ)*cols).toNat =
        src+_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hu := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverUpdate.meets (d := d+1) (μ := μ₃)
      (row := src+_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i*cols) (activePtr := activePtr) (n := cols)
      S.update (matrix (_root_.ThreeSum.BooleanGreedy.choice matrix rows cols i)) (_root_.ThreeSum.BooleanGreedy.active matrix rows cols i) hw hrowSpace
      hactiveSpace (Or.inl hrow) hrowRead hactive₃ (hmatrix _ hchoice)
      (fun j _ => _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.active_le matrix rows cols i j) hword
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hu _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hu ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselected', haddr, μ₃, _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hselected', haddr, μ₃, _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselected', haddr, μ₃, _root_.ThreeSum.LightCoverGreedy.roundTime, _root_.ThreeSum.LightCoverSelect.time, _root_.ThreeSum.LightCoverScores.time, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightCoverUpdate.time, _root_.ThreeSum.LightMinimum.time, _root_.ThreeSum.LightCoverGreedy.out] <;> omega)
       on_goal -1 => (rintro vnew μ₄ ⟨hnewActive, hkeep₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,selected,vnew,μ₄,by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rw [hnewActive j hj,_root_.ThreeSum.BooleanGreedy.active_succ hrows hmatrix i j hj]
    · exact hchoices₃.of_sameOutside hkeep₄ (Or.inr (by unfold _root_.ThreeSum.LightCoverGreedy.out; omega))
    · intro a ha
      rw [hkeep₄ _ (by unfold _root_.ThreeSum.LightCoverGreedy.total at ha; omega)]
      exact hkeep₃ a ha
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ _ _ ⟨r,v,μ',rfl,_,_,_⟩
    simp
  · rintro σ ⟨r,v,μ',rfl,hactive,written,kept⟩
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightCoverGreedy.out activePtr rows cols : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum.LightCoverGreedy.roundTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    exact ⟨rfl,written,hactive,kept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets__implementation_46d0bbee34) := (@ThreeSum1960614.Machine.ThreeSum.LightCoverGreedy.Procs.meets__implementation_46d0bbee34)

#print axioms solution
