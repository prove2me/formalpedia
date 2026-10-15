-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:11:34.628962+00:00
-- url     : https://prove2.me/submissions/958e9fb4-d367-44cd-bd19-edf12499189a

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
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
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_sort_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNormalize_dedup_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightNormalize
end ThreeSum.LightNormalize
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightNormalize
end ThreeSum1960614.Machine.ThreeSum.LightNormalize

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
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize
open _root_.ThreeSum.LightNormalize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









theorem dedup_strict {L : List ℤ} (hs : L.Pairwise (· ≤ ·)) :
    L.dedup.Pairwise (· < ·) := by
  have hle := hs.sublist (List.dedup_sublist L)
  have hne := List.nodup_dedup L
  exact (List.pairwise_and_iff.mpr ⟨hle,hne⟩).imp (fun h => lt_of_le_of_ne h.1 h.2)




















end ThreeSum.LightNormalize

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightNormalize
open _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets__implementation_0ab4daed3a {pMain src dst work d : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)
    (hseg : _root_.ThreeSum1960614.Machine.Light.Seg μ src L) (hsep : src+L.length ≤ dst)
    (hwork : dst+L.length ≤ work) (hspace : _root_.ThreeSum.LightNormalize.space work L.length ≤ lim.space)
    (hd : d+L.length+Nat.clog 2 L.length+2 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,L.length,dst,work] μ (_root_.ThreeSum.LightNormalize.time L.length)
      (fun r μ' => ∃ out : List ℤ,
        r = (out.length : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst out ∧ out.Pairwise (· < ·) ∧
        out.length ≤ L.length ∧ (∀ z, z ∈ out ↔ z ∈ L) ∧
        ∀ a, a < work → (a < src ∨ src+L.length ≤ a) →
          (a < dst ∨ dst+L.length ≤ a) → μ' a = μ a) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.body _root_.ThreeSum.LightNormalize.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.sort_meets (d := d + 1) (a := src) (fr := work) C.sort hw h1 hseg (by omega) (by exact hspace) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.sort_meets (d := d + 1) (a := src) (fr := work) C.sort hw h1 hseg (by omega) (by exact hspace) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightNormalize.space]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightNormalize.space] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime, _root_.ThreeSum.LightNormalize.space] <;> omega)
     on_goal -1 => (rintro unused μ₁ ⟨⟨sorted, hsortedSeg, hperm, hsorted⟩, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hlen := hperm.length_eq
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets C.dedup hw h1 sorted μ₁ src dst (d + 1) hsorted hsortedSeg (by omega) (by unfold _root_.ThreeSum.LightNormalize.space at hspace; omega) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets C.dedup hw h1 sorted μ₁ src dst (d + 1) hsorted hsortedSeg (by omega) (by unfold _root_.ThreeSum.LightNormalize.space at hspace; omega) (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlen, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlen, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlen, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
     on_goal -1 => (rintro count μ₂ ⟨hcount, hout, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨sorted.dedup,hcount,hout,_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_strict hsorted,?_,?_,?_⟩
  · exact (List.dedup_sublist sorted).length_le.trans hlen.le
  · intro z
    exact List.mem_dedup.trans hperm.mem_iff
  · intro a ha hsrc hdst
    change μ₂ a = μ a
    rw [hkeep₂ a (by simpa [hlen] using hdst)]
    exact hkeep₁ a ⟨ha,hsrc⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets__implementation_0ab4daed3a) := (@ThreeSum1960614.Machine.ThreeSum.LightNormalize.Procs.meets__implementation_0ab4daed3a)

#print axioms solution
