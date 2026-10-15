-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:33.085141+00:00
-- url     : https://prove2.me/submissions/6edfe871-077b-4b8d-8beb-7671d5a129f2

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverHashHistogram_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverRow_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightDecode_Procs_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverCandidate
end ThreeSum.LightLocalCoverCandidate
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.WeightEnumeration
end ThreeSum.WeightEnumeration
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.WeightEnumeration
end ThreeSum1960614.Machine.ThreeSum.WeightEnumeration

namespace ThreeSum1960614.Machine

/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration
open _root_.ThreeSum.WeightEnumeration


open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]



































theorem digit_lt {p width k coordinate : ℕ} (hp : 0 < p) : _root_.ThreeSum.WeightEnumeration.digit p width k coordinate < p :=
  Nat.mod_lt _ hp











end ThreeSum.WeightEnumeration

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
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram
open _root_.ThreeSum.LightHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem count_le (key : ℕ → ℕ) (r i : ℕ) : _root_.ThreeSum.LightHistogram.count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)















end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Costed signed residue conversion

This loop uses the benchmark's proved division-free remainder procedure.
Its sign argument supports either an ordinary histogram or a histogram of
the negated original integers. All source multiplicities are retained.
The logarithmic scratch region is reused for each input element.
-/

namespace ThreeSum.LightResidues
open _root_.ThreeSum.LightResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem residue_cast {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (_root_.ThreeSum.LightResidues.residue p c x : ℤ) = (c * x) % (p : ℤ) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by exact_mod_cast hp.ne')

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightLocalCoverCandidate
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets__implementation_ea1483d63a {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ coef) (hbits : bitPtr+n*L ≤ coef) (hcoef : coef+2*L ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+p ≤ hist1) (hhist1 : hist1+p ≤ dst) (hdst : dst+p*p ≤ work)
    (hword : (_root_.ThreeSum.LightLocalCoverCandidate.word L n p cap index : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) index (2*i))
    (hw1 : ∀ i < L, w1 i = _root_.ThreeSum.WeightEnumeration.digit p (2*L) index (2*i+1)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,p,index,n,cap,masks,bitPtr,coef,raw0,raw1,hist0,hist1,dst,work] μ
      (_root_.ThreeSum.LightLocalCoverCandidate.time L n p index)
      (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightDecode.Rows μ' coef L p index ∧
        (∀ r < p,
          μ' (hist0+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
          μ' (hist1+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
        (∀ r < p*p, μ' (dst+r) = (_root_.ThreeSum.LightLocalCoverCandidate.entry L n p cap mask bits w0 w1 r : ℤ)) ∧
        _root_.ThreeSum.LightLocalCoverCandidate.Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) := by
  have hwork : work ≤ lim.space := by unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace; omega
  have hdecodeSpace : work+(2*L+1) ≤ lim.space := by unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace; omega
  have hhashSpace : _root_.ThreeSum.LightHashHistogram.space work L p ≤ lim.space := by
    unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace
    unfold _root_.ThreeSum.LightHashHistogram.space
    omega
  have hrowSpace : work+2*(n*n) ≤ lim.space := by unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum.LightLocalCoverCandidate.word L n p cap index) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hdecodeWord := hbudget (_root_.ThreeSum.LightWeightDecode.word L p index) (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word; omega)
  have hhashWord := hbudget (_root_.ThreeSum.LightHashHistogram.word L p p) (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word; omega)
  have hrowWord := hbudget (_root_.ThreeSum.LightPairFlags.word L n p cap) (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word; omega)
  have hindexWord := hbudget index (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightWeightDecode.word _root_.ThreeSum.LightWeightRow.word; omega)
  have hnWord := hbudget n (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word; omega)
  have hb0 : ∀ i < L, w0 i ≤ p := by
    intro i hi
    rw [hw0 i hi]
    exact Nat.le_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.digit_lt hp)
  have hb1 : ∀ i < L, w1 i ≤ p := by
    intro i hi
    rw [hw1 i hi]
    exact Nat.le_of_lt (_root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.digit_lt hp)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.body _root_.ThreeSum.LightLocalCoverCandidate.time
  have hdcall := S.decode.meets (d := d+1) (μ := μ) (L := L) (p := p) (k := index)
    (dst := coef) (work := work) hw (by omega) (by omega) (by omega) hdecodeSpace hdecodeWord
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hdcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hdcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;> omega)
     on_goal -1 => (rintro value₀ μ₁ ⟨hrows, _, hkeep₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hmask₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₀ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hmaskRead i hi
  have hc0 : ∀ i < L, μ₁ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).1,hw0 i hi]
  have hc1 : ∀ i < L, μ₁ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).2,hw1 i hi]
  have hlcall := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₁)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw0) (codes := raw0+n)
    (hist := hist0) (src0 := coef) (src1 := coef+L) (work := work) mask w0 w1
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₁ hmaskLt hc0 hc1 hb0 hb1
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hlcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hlcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;> omega)
     on_goal -1 => (rintro value₁ μ₂ ⟨hleftCodes, hleftCounts, hkeep₁, hpres₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hmask₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hmask₁ i hi
  have hc0₂ : ∀ i < L, μ₂ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc0 i hi
  have hc1₂ : ∀ i < L, μ₂ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc1 i hi
  have hrcall := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₂)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw1) (codes := raw1+n)
    (hist := hist1) (src0 := coef+L) (src1 := coef) (work := work) mask w1 w0
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₂ hmaskLt hc1₂ hc0₂ hb1 hb0
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;> omega)
     on_goal -1 => (rintro value₂ μ₃ ⟨hrightCodes, hrightCounts, hkeep₂, hpres₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hleftCodes₃ : ∀ i < n, μ₃ (raw0+n+i) = (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1 i : ℤ) := by
    intro i hi
    rw [hkeep₂ _ (by omega)]
    exact hleftCodes i hi
  have hleftCounts₃ : ∀ r < p,
      μ₃ (hist0+r) = (_root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n : ℤ) := by
    intro r hr
    rw [hpres₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hleftCounts r hr
  have hbits₃ : ∀ i < n, ∀ j < L, μ₃ (bitPtr+i*L+j) = (bits i j : ℤ) := by
    intro i hi j hj
    have hm := Nat.mul_le_mul_right L (show i+1 ≤ n by omega)
    have ha : bitPtr+i*L+j < coef := by nlinarith
    rw [hkeep₂ _ (by omega),hkeep₁ _ (by omega),hkeep₀ _ ⟨by omega,Or.inl ha⟩]
    exact hbitsRead i hi j hj
  have hrowcall := S.row.meets (d := d+1) (μ := μ₃) (bitPtr := bitPtr)
    (leftPtr := raw0+n) (rightPtr := raw1+n) (leftHist := hist0) (rightHist := hist1)
    (dst := dst) (n := n) (L := L) (p := p) (cap := cap) (keys := work)
    bits (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) (_root_.ThreeSum.LightHashHistogram.code L p mask w1 w0)
    (fun r => _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w0 w1) r n)
    (fun r => _root_.ThreeSum.LightHistogram.count (_root_.ThreeSum.LightHashHistogram.code L p mask w1 w0) r n)
    hw (by omega) hn hp (by omega) (by omega) (by omega) (by omega) (by omega) hdst hrowSpace hrowWord
    hbits₃ hbitsValue hleftCodes₃ hrightCodes
    (fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp 1 _) (fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hp 1 _)
    hleftCounts₃ hrightCounts (fun r _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le _ r n)
    (fun r _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_le _ r n)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrowcall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrowcall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightWeightDecode.time, _root_.ThreeSum.LightWeightRow.time, _root_.ThreeSum.LightRadixDigit.time, _root_.ThreeSum.LightHashHistogram.time, _root_.ThreeSum.LightLocalCoverRow.time] <;> omega)
     on_goal -1 => (rintro value₃ μ₄ ⟨hout, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,?_,hout,?_⟩
  · intro i hi
    constructor
    · change μ₄ (coef+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).1
    · change μ₄ (coef+L+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).2
  · intro r hr
    constructor
    · change μ₄ (hist0+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hleftCounts₃ r hr
    · change μ₄ (hist1+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hrightCounts r hr
  · intro a ha hc hr0 hr1 hh0 hh1 hd
    change μ₄ a = μ a
    rw [hkeep₃ a ⟨ha,hd⟩,hpres₂ a ha (by omega) (by omega) hh1,
      hpres₁ a ha (by omega) (by omega) hh0]
    exact hkeep₀ a ⟨ha,hc⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets__implementation_ea1483d63a) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverCandidate.Procs.meets__implementation_ea1483d63a)

#print axioms solution
