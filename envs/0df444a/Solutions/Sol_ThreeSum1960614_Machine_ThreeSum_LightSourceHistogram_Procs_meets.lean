-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:17.497554+00:00
-- url     : https://prove2.me/submissions/49e192a2-1eff-4aea-8b0e-47e13035eea1

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHistogram_histogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceResidues_ends

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSourceHistogram
end ThreeSum.LightSourceHistogram
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram
end ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues

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
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : _root_.ThreeSum.LightSourceResidues.key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm] at h
  exact_mod_cast h











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body pEmod)) (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space) (hsep : _root_.Light.Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,n,p,m,work,shift] μ (_root_.ThreeSum.LightSourceResidues.time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
      _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst n) := by
  exact _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends hem hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues)







end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets__implementation_6ed7f15bf2 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {src hist n p m codes work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+n ≤ codes) (hhist : hist+m ≤ codes) (hcodes : codes+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,hist,n,p,m,codes,work,shift] μ (_root_.ThreeSum.LightSourceHistogram.time n p m U D)
      (fun _ ν =>
        (∀ i < n, ν (codes+i) =
          (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        (∀ r < m, ν (hist+r) = (_root_.ThreeSum.LightHistogram.count
          (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i))) r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν codes hist m) := by
  have hwork : work ≤ lim.space := by
    unfold _root_.ThreeSum.LightSourceResidues.space at hspace
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.body _root_.ThreeSum.LightSourceHistogram.time
  have hkeys := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.meets (d := d+1) (μ := μ)
    (src := src) (dst := codes) (n := n) (p := p) (m := m) (work := work)
    (U := U) (D := D) (shift := shift) S.keys S.emod hw hd hp hm
    (by omega) hcodes hspace (Or.inl hsrc) hshift hword hvalues
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hkeys _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hkeys ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨keys, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hhistogram := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.histogram_meets (d := d+1) (μ := ν₁)
    (src := codes) (dst := hist) (n := n) (p := m) S.histogram S.fill
    (fun i => _root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i))) hw hd
    (by omega) (by omega) (Or.inr hhist) keys
    (fun i _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_lt hm shift (μ (src+i)))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hhistogram _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hhistogram ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceResidues.time, _root_.ThreeSum.LightResidues.residueBudget, _root_.ThreeSum.LightHistogram.histogramTime, _root_.ThreeSum.LightHistogram.countTime] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨counts, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,counts,?_⟩
  · intro i hi
    exact (kept₂ _ (Or.inr (by omega))).trans (keys i hi)
  · intro a ⟨ha,hout⟩
    exact (kept₂ a hout).trans (kept₁ a ⟨by omega,Or.inl ha⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets__implementation_6ed7f15bf2) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceHistogram.Procs.meets__implementation_6ed7f15bf2)

#print axioms solution
