-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:44:50.449506+00:00
-- url     : https://prove2.me/submissions/280126fe-00db-4a3d-802d-b14245ec94e0

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandEnumeration_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.LightHeaderBands
end ThreeSum.LightHeaderBands
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightHeaderBands
end ThreeSum1960614.Machine.ThreeSum.LightHeaderBands

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

open _root_.ThreeSum.LightHeaderBands
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets__implementation_83d6cf76a7 {pMain a b c nA nB nC dst U d : ℕ} {μ : ℕ → ℤ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs P pMain) (A B C : _root_.ThreeSum.BandEnumeration.Family)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+2+nA+A.size ≤ dst) (hb : b+2+nB+B.size ≤ dst)
    (hc : c+2+nC+C.size ≤ dst)
    (hspace : _root_.ThreeSum.LightBandEnumeration.space dst A.size B.size C.size ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandEnumeration.word A.size B.size C.size U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+5 ≤ lim.depth)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ a nA A) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ b nB B) (hC : _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.At μ c nC C)
    (hAU : _root_.ThreeSum.LightBandEnumeration.Bounded A U) (hBU : _root_.ThreeSum.LightBandEnumeration.Bounded B U)
    (hCU : _root_.ThreeSum.LightBandEnumeration.Bounded C U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,dst] μ (_root_.ThreeSum.LightHeaderBands.time A.size B.size C.size)
      (fun r μ' => r = (_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.Tables μ' dst A B C ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' dst) := by
  obtain ⟨han,has,hA⟩ := hA
  obtain ⟨hbn,hbs,hB⟩ := hB
  obtain ⟨hcn,hcs,hC⟩ := hC
  have hspace' : dst+_root_.ThreeSum.LightBandEnumeration.count A.size B.size C.size+
      _root_.ThreeSum.LightBandEnumeration.width A.size B.size C.size+1 ≤ lim.space := hspace
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.body _root_.ThreeSum.LightHeaderBands.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.enumerate.meets (d := d + 1) A B C hw (by omega) ha (by omega) hb (by omega) hc hspace hword (by omega) hA hB hC hAU hBU hCU) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.enumerate.meets (d := d + 1) A B C hw (by omega) ha (by omega) hb (by omega) hc hspace hword (by omega) hA hB hC hAU hBU hCU) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, han, has, hbn, hbs, hcn, hcs, _root_.ThreeSum.LightBandEnumeration.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [han, has, hbn, hbs, hcn, hcs, _root_.ThreeSum.LightBandEnumeration.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, han, has, hbn, hbs, hcn, hcs, _root_.ThreeSum.LightBandEnumeration.time] <;> omega)
     on_goal -1 => (rintro result μ' hresult; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact hresult
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets__implementation_83d6cf76a7) := (@ThreeSum1960614.Machine.ThreeSum.LightHeaderBands.Procs.meets__implementation_83d6cf76a7)

#print axioms solution
