-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:10:14.600344+00:00
-- url     : https://prove2.me/submissions/7540d2b9-f549-4b3c-84e1-1798114b4e76

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.OfFn
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketFromHistogram_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBucketBuild
end ThreeSum.LightSourceBucketBuild
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBucketBuild
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs.meets__implementation_da4bc4df60 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs P pMain)
    {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hkeys : keys+N ≤ offsets) (hhist : hist+M ≤ offsets)
    (hsep : _root_.Light.Apart keys N hist M)
    (hoffsets : offsets+M+1 ≤ cursor) (hcursor : cursor+M ≤ flat)
    (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,hist,offsets,cursor,flat,N,M] μ (_root_.ThreeSum.LightSourceBucketBuild.time N M)
      (fun _ ν => _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored ν key N M offsets flat ∧
        (∀ r < M, ν (hist+r) = (_root_.ThreeSum.LightHistogram.count key r N : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν hist ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν hist (flat+N-hist)) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.body _root_.ThreeSum.LightSourceBucketBuild.time
  have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets (d := d+1) C.histogram C.fill (μ := μ)
    (src := keys) (dst := hist) (n := N) (p := M) key
    hw (by omega) (by omega) (by omega) hsep hread hkey
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hh _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hh ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨counts, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hr : ∀ i < N, ν₁ (keys+i) = (key i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hread i hi)
  have hb := C.buckets.meets (d := d+1) (μ := ν₁) (keys := keys) (hist := hist)
    (offsets := offsets) (cursor := cursor) (flat := flat) (N := N) (M := M)
    key hw (by omega) hkeys hhist hoffsets hcursor hspace hkey hr counts
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime, _root_.ThreeSum.LightSourceBucketFromHistogram.time, _root_.ThreeSum.LightSourceBucketOffsets.time, _root_.ThreeSum.LightSourceBucketScatter.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨stored, kept₂, same₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨stored,?_,?_,?_⟩
  · intro r hr
    exact (kept₂ _ (by omega)).trans (counts r hr)
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a (Or.inl ha))
  · intro a ha
    exact (same₂ a (by omega)).trans (kept₁ a (by omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs.meets__implementation_da4bc4df60) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceBucketBuild.Procs.meets__implementation_da4bc4df60)

#print axioms solution
