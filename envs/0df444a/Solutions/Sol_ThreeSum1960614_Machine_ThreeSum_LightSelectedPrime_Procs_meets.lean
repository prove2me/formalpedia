-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:40.135428+00:00
-- url     : https://prove2.me/submissions/7e6846ad-9968-47ac-99fa-181ece14b38d

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_sqrt_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPrimePool_Procs_meets
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPrimePool
end ThreeSum.LightPrimePool
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSelectedPrime
end ThreeSum.LightSelectedPrime
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPrimePool
end ThreeSum1960614.Machine.ThreeSum.LightPrimePool
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime
end ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

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
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool
open _root_.ThreeSum.LightPrimePool


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000















theorem values_increasing (y : ℕ) : (_root_.ThreeSum.LightPrimePool.values y).Pairwise (· < ·) := _root_.ThreeSum.LightPrimePool.prefix_increasing y (3*y)











theorem prime_spec {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y i) ∧ y < _root_.ThreeSum.LightPrimePool.prime y i ∧ _root_.ThreeSum.LightPrimePool.prime y i ≤ 4*y :=
  _root_.ThreeSum.LightPrimePool.mem_values.mp (_root_.ThreeSum.LightPrimePool.prime_mem hi)



theorem prime_strictly_increasing {y i j : ℕ}
    (hi : i < _root_.ThreeSum.LightPrimePool.size y) (hj : j < _root_.ThreeSum.LightPrimePool.size y) (hij : i < j) : _root_.ThreeSum.LightPrimePool.prime y i < _root_.ThreeSum.LightPrimePool.prime y j := by
  unfold _root_.ThreeSum.LightPrimePool.prime
  rw [List.getD_eq_getElem _ _ hi,List.getD_eq_getElem _ _ hj]
  exact List.pairwise_iff_getElem.mp (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_increasing y) i j hi hj hij

theorem values_nonempty {y : ℕ} (hy : 0 < y) : _root_.ThreeSum.LightPrimePool.values y ≠ [] := by
  obtain ⟨p,hp,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ _root_.ThreeSum.LightPrimePool.values y := _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hp,hlo,by omega⟩
  intro heq
  simpa only [heq,List.not_mem_nil] using hmem

theorem size_pos {y : ℕ} (hy : 0 < y) : 0 < _root_.ThreeSum.LightPrimePool.size y :=
  List.length_pos_iff.mpr (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.values_nonempty hy)

theorem prime_zero_le {y i : ℕ} (hi : i < _root_.ThreeSum.LightPrimePool.size y) : _root_.ThreeSum.LightPrimePool.prime y 0 ≤ _root_.ThreeSum.LightPrimePool.prime y i := by
  by_cases heq : i = 0
  · simp [heq]
  · exact (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_strictly_increasing (by omega) hi (by omega)).le

theorem prime_zero_le_mem {y p : ℕ} (hp : p ∈ _root_.ThreeSum.LightPrimePool.values y) : _root_.ThreeSum.LightPrimePool.prime y 0 ≤ p := by
  obtain ⟨i,hi,heq⟩ := List.mem_iff_getElem.mp hp
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_zero_le (y := y) (i := i) hi
  simpa only [_root_.ThreeSum.LightPrimePool.prime,List.getD_eq_getElem _ _ hi,heq] using hm

theorem prime_zero_spec {y : ℕ} (hy : 0 < y) :
    Nat.Prime (_root_.ThreeSum.LightPrimePool.prime y 0) ∧ y < _root_.ThreeSum.LightPrimePool.prime y 0 ∧ _root_.ThreeSum.LightPrimePool.prime y 0 ≤ 2*y := by
  have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_spec (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hy)
  obtain ⟨p,hpr,hlo,hhi⟩ := Nat.exists_prime_lt_and_le_two_mul y hy.ne'
  have hmem : p ∈ _root_.ThreeSum.LightPrimePool.values y := _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hpr,hlo,by omega⟩
  exact ⟨hp.1,hp.2.1,(_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_zero_le_mem hmem).trans hhi⟩













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightPrimePool

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing the deterministic square-root prime selection

The candidate pool is scanned by the verified primality program. Its first
entry is exactly the minimum used by `LocalCoverBounds.selectedPrime`.
The input threshold is positive; the routine has no primality oracle or
externally supplied list of candidates.
-/

namespace ThreeSum.LightSelectedPrime
open _root_.ThreeSum.LightSelectedPrime


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues

set_option maxHeartbeats 1000000

theorem prime_zero_eq_selectedPrime (N : ℕ) :
    _root_.ThreeSum.LightPrimePool.prime (_root_.ThreeSum.LocalCoverBounds.rootCeiling N) 0 = _root_.ThreeSum.LocalCoverBounds.selectedPrime N := by
  apply Nat.le_antisymm
  · have hs := _root_.ThreeSum.LocalCoverBounds.selectedPrime_spec N
    apply _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_zero_le_mem
    exact _root_.ThreeSum.LightPrimePool.mem_values.mpr ⟨hs.1,hs.2.1,by omega⟩
  · unfold _root_.ThreeSum.LocalCoverBounds.selectedPrime
    apply Finset.min'_le
    exact _root_.ThreeSum.LocalCoverBounds.mem_primeCandidates.mpr
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.prime_zero_spec (_root_.ThreeSum.LocalCoverBounds.rootCeiling_pos N))









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightSelectedPrime

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSelectedPrime
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
set_option maxHeartbeats 1000000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs.meets__implementation_3eb529a2f8 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs P pMain)
    {μ : ℕ → ℤ} {N free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hN : 0 < N) (hspace : _root_.ThreeSum.LightSelectedPrime.space free N ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSelectedPrime.word N : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [N,free] μ (_root_.ThreeSum.LightSelectedPrime.time N)
      (fun r μ' => r = (_root_.ThreeSum.LocalCoverBounds.selectedPrime N : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' free (_root_.ThreeSum.LightPrimePool.values (_root_.ThreeSum.LocalCoverBounds.rootCeiling N)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' free) := by
  have hypos := _root_.ThreeSum.LocalCoverBounds.rootCeiling_pos N
  have hy : _root_.ThreeSum.LocalCoverBounds.rootCeiling N ≤ N+1 := by
    unfold _root_.ThreeSum.LocalCoverBounds.rootCeiling
    have hh := Nat.sqrt_le_self (N-1)
    omega
  have hwordZ : 100*((N : ℤ)+1) ≤ lim.word := by exact_mod_cast hword
  have hsub : (N : ℤ)-1 = ((N-1 : ℕ) : ℤ) := by omega
  have hrootWord : (_root_.ThreeSum.LocalCoverBounds.rootCeiling N : ℤ) ≤ lim.word := by omega
  have hpoolWord : (_root_.ThreeSum.LightPrimePool.word (_root_.ThreeSum.LocalCoverBounds.rootCeiling N) : ℤ) ≤ lim.word := by
    unfold _root_.ThreeSum.LightPrimePool.word
    push_cast
    omega
  have hfree : free < lim.space := by
    unfold _root_.ThreeSum.LightSelectedPrime.space _root_.ThreeSum.LightPrimePool.space at hspace
    omega
  have hselectedWord : (_root_.ThreeSum.LocalCoverBounds.selectedPrime N : ℤ) ≤ lim.word := by
    have hp := (_root_.ThreeSum.LocalCoverBounds.selectedPrime_spec N).2.2
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.body _root_.ThreeSum.LightSelectedPrime.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := N - 1) S.sqrt μ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := N - 1) S.sqrt μ (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsub, _root_.ThreeSum.LightPrimePool.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hsub, _root_.ThreeSum.LightPrimePool.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsub, _root_.ThreeSum.LightPrimePool.time] <;> omega)
     on_goal -1 => (rintro root μ₁ ⟨hr, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  have hr' : root+1 = (_root_.ThreeSum.LocalCoverBounds.rootCeiling N : ℤ) := by
    simpa [_root_.ThreeSum.LocalCoverBounds.rootCeiling] using congrArg (fun z : ℤ => z+1) hr
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LocalCoverBounds.rootCeiling N : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hr', _root_.ThreeSum.LightPrimePool.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hr', _root_.ThreeSum.LightPrimePool.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr', _root_.ThreeSum.LightPrimePool.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.pool.meets (d := d + 1) hw hd hypos hspace hpoolWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.pool.meets (d := d + 1) hw hd hypos hspace hpoolWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPrimePool.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPrimePool.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPrimePool.time] <;> omega)
     on_goal -1 => (rintro count μ₂ ⟨hc, hseg, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hlen : 0 < (_root_.ThreeSum.LightPrimePool.values (_root_.ThreeSum.LocalCoverBounds.rootCeiling N)).length :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightPrimePool.size_pos hypos
  have hfirst : μ₂ free = (_root_.ThreeSum.LocalCoverBounds.selectedPrime N : ℤ) := by
    have hh := hseg 0 (by simp; exact hlen)
    rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.prime_zero_eq_selectedPrime]
    change μ₂ free = ((_root_.ThreeSum.LightPrimePool.values (_root_.ThreeSum.LocalCoverBounds.rootCeiling N)).getD 0 0 : ℤ)
    rw [List.getD_eq_getElem _ _ hlen]
    simpa using hh
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LocalCoverBounds.selectedPrime N : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfirst, _root_.ThreeSum.LightPrimePool.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfirst, _root_.ThreeSum.LightPrimePool.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfirst, _root_.ThreeSum.LightPrimePool.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨rfl,hseg,hkept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs.meets__implementation_3eb529a2f8) := (@ThreeSum1960614.Machine.ThreeSum.LightSelectedPrime.Procs.meets__implementation_3eb529a2f8)

#print axioms solution
