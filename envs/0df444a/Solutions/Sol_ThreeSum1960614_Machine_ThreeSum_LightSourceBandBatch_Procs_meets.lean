-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:24:15.568882+00:00
-- url     : https://prove2.me/submissions/ddb2b0a8-dca7-41d4-88a2-a41fd1e9a036

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
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
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
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
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBandStep_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBandData_At_transfer

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBandBatch
end ThreeSum.LightSourceBandBatch
namespace ThreeSum.SourceBandData
end ThreeSum.SourceBandData
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandData
end ThreeSum1960614.Machine.ThreeSum.SourceBandData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets

namespace ThreeSum1960614.Machine

/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition
open _root_.ThreeSum.BandPartition






theorem size_le (n g : ℕ) : _root_.ThreeSum.BandPartition.size n g ≤ n := by
  unfold _root_.ThreeSum.BandPartition.size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega

























end ThreeSum.BandPartition

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

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

/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandLayout


open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets




















theorem hist_mono (base n g m : ℕ) : Monotone (_root_.ThreeSum.SourceBandLayout.hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem data_le_hist (base n g m i : ℕ) : _root_.ThreeSum.SourceBandLayout.data base n g ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m i :=
  Nat.le_add_right _ _

theorem flat_end (base n g m i : ℕ) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g = _root_.ThreeSum.SourceBandLayout.hist base n g m (i+1) := by
  unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.stride
  ring

theorem header_end {base n g m i : ℕ} (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    base+6*i+6 ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m i := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m i
  unfold _root_.ThreeSum.SourceBandLayout.data at hb
  omega



theorem flat_end_le_later {base n g m i k : ℕ} (hik : i < k) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g ≤ _root_.ThreeSum.SourceBandLayout.hist base n g m k := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.hist_mono base n g m (by omega)















end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained original-band headers, histograms, and physical position fibers -/

namespace ThreeSum.SourceBandData
open _root_.ThreeSum.SourceBandData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout





theorem At.of_later {μ ν : ℕ → ℤ} {f : ℕ → ℤ} {base n g p m i k : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At μ f base n g p m shift i)
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.SourceBandLayout.hist base n g m k) (base+6*k) 6)
    (hm : 0 < m) (hik : i < k) (hk : k < _root_.ThreeSum.BandPartition.size n g) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At ν f base n g p m shift i := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.header_end (m := m) (base := base) hk
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m i
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_later (base := base) (n := n) (g := g) (m := m) hik
  unfold _root_.ThreeSum.SourceBandLayout.data at hb
  apply H.transfer hm
  · intro q hq
    exact K _ ⟨by omega,Or.inl (by omega)⟩
  · intro x hx hxe
    exact K _ ⟨by omega,Or.inr (by omega)⟩











end ThreeSum.SourceBandData

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceBandBatch
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Procs.meets__implementation_f63216b660 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Procs P pMain)
    {μ : ℕ → ℤ} {src n g p m base U D : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+4 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base)
    (hspace : _root_.ThreeSum.LightSourceResidues.space (_root_.ThreeSum.SourceBandLayout.work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [src,n,g,p,m,shift,base,_root_.ThreeSum.SourceBandLayout.cap n g,_root_.ThreeSum.BandPartition.size n g,_root_.ThreeSum.SourceBandLayout.data base n g,_root_.ThreeSum.SourceBandLayout.stride n g m,_root_.ThreeSum.SourceBandLayout.work base n g m]
      μ (_root_.ThreeSum.LightSourceBandBatch.time n g p m U D) (fun _ ν =>
        (∀ i < _root_.ThreeSum.BandPartition.size n g, _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandData.At ν f base n g p m shift i) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by
  have hwork : _root_.ThreeSum.SourceBandLayout.work base n g m ≤ lim.space := by unfold _root_.ThreeSum.LightSourceResidues.space at hspace; omega
  have hbase : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m (_root_.ThreeSum.BandPartition.size n g)
    unfold _root_.ThreeSum.SourceBandLayout.data at hh
    exact (by omega : base ≤ hist base n g m (size n g))
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le n g
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.body _root_.ThreeSum.LightSourceBandBatch.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Inv μ f src n g p m base shift) (_root_.ThreeSum.BandPartition.size n g)
    (_root_.ThreeSum.LightSourceBandStep.time n g p m U D+172) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
        ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hread' : ∀ j < n, ν (src+j)=f j := by
      intro j hj
      exact (kept _ (by omega)).trans (hread j hj)
    have hrun := C.step.meets (d := d+1) (μ := ν) (src := src) (n := n) (g := g)
      (p := p) (m := m) (base := base) (U := U) (D := D) (shift := shift) (i := i)
      f hw (by omega) hg hp hm hi hsrc hspace hshift hword hread' hvalues
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro s ν' ⟨stored, kept'⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,s,ν',by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (written j hj).of_later kept' hm hj hi
      · exact stored
    · intro x hx
      have hb := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.data_le_hist base n g m i
      unfold _root_.ThreeSum.SourceBandLayout.data at hb
      exact (kept' x ⟨by omega,Or.inl (by omega)⟩).trans (kept x hx)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Procs.meets__implementation_f63216b660) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandBatch.Procs.meets__implementation_f63216b660)

#print axioms solution
