-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:24:17.350403+00:00
-- url     : https://prove2.me/submissions/13f2e81d-0cc0-4d9c-8c6d-edc72a303728

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverCandidate_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverMatrix
end ThreeSum.LightLocalCoverMatrix
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix

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

/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





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

open _root_.ThreeSum.LightLocalCoverMatrix
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets__implementation_7447d6d6fe {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+5 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ maps) (hbits : bitPtr+n*L ≤ maps) (hmaps : maps+N*(2*L) ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+N*p ≤ hist1) (hhist1 : hist1+N*p ≤ dst) (hdst : dst+N*(p*p) ≤ work)
    (hword : (_root_.ThreeSum.LightLocalCoverCandidate.word L n p cap N : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ j < N, ∀ i < L, w0 j i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) j (2*i))
    (hw1 : ∀ j < N, ∀ i < L, w1 j i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) j (2*i+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,p,N,n,cap,masks,bitPtr,maps,raw0,raw1,hist0,hist1,dst,work] μ (_root_.ThreeSum.LightLocalCoverMatrix.time L n p N)
      (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Tables μ' L n p cap maps hist0 hist1 dst mask bits w0 w1 N ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' maps) := by
  have hwork : work ≤ lim.space := by unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum.LightLocalCoverCandidate.word L n p cap N) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hNWord := hbudget N (by
    unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightWeightDecode.word _root_.ThreeSum.LightWeightRow.word
    omega)
  have hnWord := hbudget n (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hWWord := hbudget (2*L) (by
    unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightWeightDecode.word _root_.ThreeSum.LightWeightRow.word
    omega)
  have h2Word := hbudget 2 (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hWWordZ : (2 : ℤ)*L ≤ lim.word := by exact_mod_cast hWWord
  have hp2Word := hbudget (p*p) (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hp2WordZ : (p : ℤ)*p ≤ lim.word := by exact_mod_cast hp2Word
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.body _root_.ThreeSum.LightLocalCoverMatrix.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (p * p : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightLocalCoverCandidate.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightLocalCoverCandidate.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightLocalCoverCandidate.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Inv μ L n p cap N masks bitPtr maps raw0 raw1 hist0 hist1 dst work mask bits w0 w1)
    N (_root_.ThreeSum.LightLocalCoverCandidate.time L n p N+192) ?_ ?_ ?_ ?_
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightLocalCoverCandidate.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightLocalCoverCandidate.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))))
  · refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro j hj; omega
  · rintro i _ hi _ ⟨r,μ',rfl,written,kept⟩
    have himaps := Nat.mul_le_mul_right (2*L) (show i+1 ≤ N by omega)
    have hihist := Nat.mul_le_mul_right p (show i+1 ≤ N by omega)
    have himatrix := Nat.mul_le_mul_right (p*p) (show i+1 ≤ N by omega)
    simp only [Nat.add_mul,one_mul] at himaps hihist himatrix
    have hcoef : maps+i*(2*L)+2*L ≤ raw0 := by omega
    have hlhist : hist0+i*p+p ≤ hist1+i*p := by omega
    have hrhist : hist1+i*p+p ≤ dst+i*(p*p) := by omega
    have hrow : dst+i*(p*p)+p*p ≤ work := by omega
    have hmulCoef : ((i*(2*L) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(2*L) ≤ lim.space)).trans hw
    have hmulHist : ((i*p : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*p ≤ lim.space)).trans hw
    have hmulMatrix : ((i*(p*p) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (by omega : i*(p*p) ≤ lim.space)).trans hw
    have hcoefAddr : ((maps : ℤ)+(i : ℤ)*(2*(L : ℤ))).toNat = maps+i*(2*L) := by
      norm_cast
    have hlhistAddr : ((hist0 : ℤ)+(i : ℤ)*p).toNat = hist0+i*p := by norm_cast
    have hrhistAddr : ((hist1 : ℤ)+(i : ℤ)*p).toNat = hist1+i*p := by norm_cast
    have hmatrixAddr : ((dst : ℤ)+(i : ℤ)*((p : ℤ)*p)).toNat = dst+i*(p*p) := by norm_cast
    have hmask' : ∀ j < n, μ' (masks+j) = (mask j : ℤ) := by
      intro j hj
      rw [kept _ (by omega)]
      exact hmaskRead j hj
    have hbits' : ∀ a < n, ∀ j < L, μ' (bitPtr+a*L+j) = (bits a j : ℤ) := by
      intro a ha j hj
      have hm := Nat.mul_le_mul_right L (show a+1 ≤ n by omega)
      simp only [Nat.add_mul,one_mul] at hm
      have hab : bitPtr+a*L+j < maps := by omega
      rw [kept _ hab]
      exact hbitsRead a ha j hj
    have hword' : (_root_.ThreeSum.LightLocalCoverCandidate.word L n p cap i : ℤ) ≤ lim.word := by
      apply hbudget
      unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightWeightDecode.word _root_.ThreeSum.LightWeightRow.word
      omega
    have htime' : _root_.ThreeSum.LightLocalCoverCandidate.time L n p i ≤ _root_.ThreeSum.LightLocalCoverCandidate.time L n p N := by
      unfold _root_.ThreeSum.LightLocalCoverCandidate.time _root_.ThreeSum.LightWeightDecode.time _root_.ThreeSum.LightWeightRow.time _root_.ThreeSum.LightRadixDigit.time
      gcongr
    have hcall := S.candidate.meets (d := d+1) (μ := μ') (L := L) (n := n) (p := p) (cap := cap)
      (index := i) (masks := masks) (bitPtr := bitPtr) (coef := maps+i*(2*L))
      (raw0 := raw0) (raw1 := raw1) (hist0 := hist0+i*p) (hist1 := hist1+i*p)
      (dst := dst+i*(p*p)) (work := work) mask (w0 i) (w1 i) bits
      hw (by omega) hp hn hspace (by omega) (by omega) hcoef hraw0 (by omega) hlhist hrhist hrow
      hword' hmask' hmaskLt hbits' hbitsValue (hw0 i hi) (hw1 i hi)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((hcall.mono_time htime') _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall.mono_time htime') ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr, _root_.ThreeSum.LightLocalCoverCandidate.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr, _root_.ThreeSum.LightLocalCoverCandidate.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcoefAddr, hlhistAddr, hrhistAddr, hmatrixAddr, _root_.ThreeSum.LightLocalCoverCandidate.time] <;> omega)
       on_goal -1 => (rintro value μ₁ ⟨hcoeffs, hcounts, hentry, hpres⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hprevCoef : ∀ j < i, ∀ a < 2*L,
        μ₁ (maps+j*(2*L)+a) = μ' (maps+j*(2*L)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (2*L) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : maps+j*(2*L)+a < maps+i*(2*L) := by omega
      exact hpres _ (by omega) (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevLeft : ∀ j < i, ∀ a < p,
        μ₁ (hist0+j*p+a) = μ' (hist0+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist0+j*p+a < hist0+i*p := by omega
      have hbound : hist0+j*p+a < hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inl hbefore) (Or.inl (by omega)) (Or.inl (by omega))
    have hprevRight : ∀ j < i, ∀ a < p,
        μ₁ (hist1+j*p+a) = μ' (hist1+j*p+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right p (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : hist1+j*p+a < hist1+i*p := by omega
      have hbound : hist1+j*p+a < dst := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inl hbefore) (Or.inl (by omega))
    have hprevMatrix : ∀ j < i, ∀ a < p*p,
        μ₁ (dst+j*(p*p)+a) = μ' (dst+j*(p*p)+a) := by
      intro j hj a ha
      have hjm := Nat.mul_le_mul_right (p*p) (show j+1 ≤ i by omega)
      simp only [Nat.add_mul,one_mul] at hjm
      have hbefore : dst+j*(p*p)+a < dst+i*(p*p) := by omega
      have hleft : hist0+i*p+p ≤ hist1 := by omega
      have hright : hist1+i*p+p ≤ dst := by omega
      exact hpres _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inr (by omega))
        (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl hbefore)
    refine ⟨by simp,value,μ₁,by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · obtain ⟨hc,hh,he⟩ := written j hj
        refine ⟨?_,?_,?_⟩
        · intro a ha
          constructor
          · rw [hprevCoef j hj a (by omega)]
            exact (hc a ha).1
          · have ha' : L+a < 2*L := by omega
            have hkeep := hprevCoef j hj (L+a) ha'
            rw [← Nat.add_assoc] at hkeep
            rw [hkeep]
            exact (hc a ha).2
        · intro a ha
          rw [hprevLeft j hj a ha,hprevRight j hj a ha]
          exact hh a ha
        · intro a ha
          rw [hprevMatrix j hj a ha]
          exact he a ha
      · exact ⟨hcoeffs,hcounts,hentry⟩
    · intro a ha
      rw [hpres a (by omega) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))
        (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
      exact kept a ha
  · rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets__implementation_7447d6d6fe) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMatrix.Procs.meets__implementation_7447d6d6fe)

#print axioms solution
