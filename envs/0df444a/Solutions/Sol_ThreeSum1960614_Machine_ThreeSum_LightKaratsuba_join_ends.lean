-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:40.808685+00:00
-- url     : https://prove2.me/submissions/16153ae8-eafa-4031-b1c8-884bb33fad1d

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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightArray_linear_bounded_meets

namespace Light
end Light
namespace Light.Copy
end Light.Copy
namespace Light.Fill
end Light.Fill
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
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

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
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun _ => x) (fun i hi => by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
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



































theorem window_bound {f : ℕ → ℤ} {offset n j U : ℕ}
    (hf : ∀ i < n, |f i| ≤ U) : |_root_.ThreeSum.LightKaratsuba.window f offset n j| ≤ U := by
  unfold _root_.ThreeSum.LightKaratsuba.window
  split_ifs with hj
  · exact hf _ (by omega)
  · simpa using (Nat.cast_nonneg U : (0 : ℤ) ≤ U)

theorem linear_update_full {μ μ' : ℕ → ℤ} {out src offset n N : ℕ}
    {c : ℤ} {f g : ℕ → ℤ} (hfit : offset + n ≤ N)
    (hOld : ∀ j < N, μ (out + j) = f j)
    (hSrc : ∀ i < n, μ (src + i) = g i)
    (hWrite : ∀ i < n,
      μ' (out + offset + i) = μ (out + offset + i) + c * μ (src + i))
    (hkeep : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' (out + offset) n) :
    ∀ j < N, μ' (out + j) = f j + _root_.ThreeSum.LightKaratsuba.window (fun i => c * g i) offset n j := by
  intro j hj
  unfold _root_.ThreeSum.LightKaratsuba.window
  split_ifs with hin
  · have hi : j - offset < n := by omega
    have he : out + offset + (j - offset) = out + j := by omega
    have hr := hWrite (j - offset) hi
    rw [he, hOld j hj, hSrc _ hi] at hr
    exact hr
  · have hr := hkeep (out + j) (by omega)
    simpa only [add_zero, hOld j hj] using hr





section Join

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}



end Join

section BaseCase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end BaseCase





















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

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends__implementation_1e5bd348b1 (hLinear : P[pLinear]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linearBody)
    (hFill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ}
    (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧
      |μ (work + 2 * n + i)| ≤ U)
    (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joinBody pLinear pFill)
      ⟨_root_.Light.frame [n, a, b, out, work, half, r], μ⟩ (_root_.ThreeSum.LightKaratsuba.joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = _root_.ThreeSum.LightKaratsuba.joined μ work n half j) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ σ'.mem work out (2 * n) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.joinBody
  have hU : (0 : ℤ) ≤ U := Nat.cast_nonneg U
  have hcall1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ) (srcA := work + 2 * n) (srcB := work) (dst := work + 2 * n)
    (n := n) (U := U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨(hvalues i hi).2.2, (hvalues i hi).1⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall1 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall1 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨hr₁, hk₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hz01 : ∀ i < n, μ₁ (work + i) = μ (work + i) :=
    fun i hi => hk₁ _ (by omega)
  have hz21 : ∀ i < n, μ₁ (work + n + i) = μ (work + n + i) :=
    fun i hi => hk₁ _ (by omega)
  have hm1 : ∀ i < n, |μ₁ (work + 2 * n + i)| ≤ 2 * (U : ℤ) := by
    intro i hi
    rw [hr₁ i hi]
    have hab := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have hv := hvalues i hi
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      hab.trans (by omega : |μ (work + 2 * n + i)| + |μ (work + i)| ≤ 2 * (U : ℤ))
  have hcall2 := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₁) (srcA := work + 2 * n) (srcB := work + n) (dst := work + 2 * n)
    (n := n) (U := 2 * U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by simpa using hm1 i hi, by rw [hz21 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall2 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall2 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₂ ⟨hr₂, hk₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hz02 : ∀ i < n, μ₂ (work + i) = μ (work + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz01 i hi)
  have hz22 : ∀ i < n, μ₂ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz21 i hi)
  have hmiddle : ∀ i < n, μ₂ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) := by
    intro i hi
    rw [hr₂ i hi, hr₁ i hi, hz21 i hi]
    ring
  have hm2 : ∀ i < n, |μ₂ (work + 2 * n + i)| ≤ 3 * (U : ℤ) := by
    intro i hi
    rw [hmiddle i hi]
    have h₁ := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have h₂ := abs_sub (μ (work + 2 * n + i) - μ (work + i)) (μ (work + n + i))
    have hv := hvalues i hi
    omega
  have hfill := _root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) hFill (μ := μ₂) (dst := out) (n := 2 * n)
    (x := 0) hw (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hfill _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hfill ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₃ ⟨hzeroSeg, hk₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hzero : ∀ j < 2 * n, μ₃ (out + j) = 0 := by
    intro j hj
    rw [hzeroSeg j (by simpa using hj)]
    exact List.getElem_replicate ..
  have hz03 : ∀ i < n, μ₃ (work + i) = μ (work + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz02 i hi)
  have hz23 : ∀ i < n, μ₃ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz22 i hi)
  have hm3 : ∀ i < n, μ₃ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => hk₃ _ (by omega)
  have hcall3 := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₃) (srcA := out) (srcB := work) (dst := out)
    (n := n) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨by rw [hzero i (by omega), abs_zero]; exact hU,
      by rw [hz03 i hi]; exact (hvalues i hi).1⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall3 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall3 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₄ ⟨hr₄, hk₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hfirst : ∀ j < 2 * n, μ₄ (out + j) = _root_.ThreeSum.LightKaratsuba.window (fun i => μ (work + i)) 0 n j := by
    have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.linear_update_full (offset := 0) (by omega : 0 + n ≤ 2 * n)
      hzero hz03 (by simpa only [Nat.add_zero] using hr₄)
      (by simpa only [Nat.add_zero] using hk₄)
    simpa only [one_mul, zero_add] using ht
  have hz24 : ∀ i < n, μ₄ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hz23 i hi)
  have hm4 : ∀ i < n, μ₄ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hm3 i hi)
  have hcall4 := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₄) (srcA := out + half) (srcB := work + 2 * n) (dst := out + half)
    (n := n) (U := 3 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + half + i = out + (half + i) by omega, hfirst _ (by omega)]
      have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.window_bound (offset := 0) (j := half + i) (fun j hj => (hvalues j hj).1)
      push_cast; omega,
      by rw [hm4 i hi]; simpa using hm2 i hi⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall4 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall4 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₅ ⟨hr₅, hk₅⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hm4' : ∀ i < n, μ₄ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) :=
    fun i hi => (hm4 i hi).trans (hmiddle i hi)
  have hsecond : ∀ j < 2 * n, μ₅ (out + j) =
      _root_.ThreeSum.LightKaratsuba.window (fun i => μ (work + i)) 0 n j +
      _root_.ThreeSum.LightKaratsuba.window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j := by
    have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.linear_update_full (by omega : half + n ≤ 2 * n) hfirst hm4' hr₅ hk₅
    simpa only [one_mul] using ht
  have hz25 : ∀ i < n, μ₅ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₅ _ (by omega)).trans (hz24 i hi)
  have hcall5 := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₅) (srcA := out + n) (srcB := work + n) (dst := out + n)
    (n := n) (U := 4 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + n + i = out + (n + i) by omega, hsecond _ (by omega)]
      have h₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.window_bound (offset := 0) (j := n + i) (fun j hj => (hvalues j hj).1)
      have h₂ : |_root_.ThreeSum.LightKaratsuba.window (fun j => μ (work + 2 * n + j) - μ (work + j) -
          μ (work + n + j)) half n (n + i)| ≤ 3 * (U : ℤ) := by
        have hv := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.window_bound (offset := half) (j := n + i) (U := 3 * U)
          (f := fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j))
          (fun j hj => by rw [← hmiddle j hj]; simpa using hm2 j hj)
        simpa using hv
      have hs := abs_add_le
        (_root_.ThreeSum.LightKaratsuba.window (fun j => μ (work + j)) 0 n (n + i))
        (_root_.ThreeSum.LightKaratsuba.window (fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j)) half n (n + i))
      push_cast; omega,
      by rw [hz25 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall5 _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall5 ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightKaratsuba.joinTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro _ μ₆ ⟨hr₆, hk₆⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  constructor
  · have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.linear_update_full (by omega : n + n ≤ 2 * n) hsecond hz25 hr₆ hk₆
    simpa only [one_mul, _root_.ThreeSum.LightKaratsuba.joined] using ht
  · intro j hj
    change μ₆ j = μ j
    rw [hk₆ j (by omega), hk₅ j (by omega), hk₄ j (by omega), hk₃ j hj.2,
      hk₂ j (by omega), hk₁ j (by omega)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends__implementation_1e5bd348b1) := (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.join_ends__implementation_1e5bd348b1)

#print axioms solution
