-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:22:09.919218+00:00
-- url     : https://prove2.me/submissions/0521baf2-df84-488c-b6b4-7dca20fe0cac

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

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightSourceBandHistSelect
end ThreeSum.LightSourceBandHistSelect
namespace ThreeSum.SourceBandLayout
end ThreeSum.SourceBandLayout
namespace ThreeSum.SourceBandPairData
end ThreeSum.SourceBandPairData
namespace ThreeSum.SourceBandPairSlices
end ThreeSum.SourceBandPairSlices
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
end ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
namespace ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
end ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































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

theorem flat_end_le_work {base n g m i : ℕ} (hi : i < _root_.ThreeSum.BandPartition.size n g) :
    _root_.ThreeSum.SourceBandLayout.flat base n g m i+_root_.ThreeSum.SourceBandLayout.cap n g ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.hist_mono base n g m (by omega)

















end ThreeSum.SourceBandLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairData


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ _root_.ThreeSum.SourceBandLayout.work base n g m := by
  unfold _root_.ThreeSum.SourceBandLayout.work _root_.ThreeSum.SourceBandLayout.hist _root_.ThreeSum.SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    _root_.ThreeSum.SourceBandPairData.leftBase base ≤ _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ∧
    _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ∧
    _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m < _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.work_ge _ _ _ _,by unfold _root_.ThreeSum.SourceBandPairData.next; omega⟩















end ThreeSum.SourceBandPairData

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Padded histogram selection for independently chosen original bands -/

namespace ThreeSum.SourceBandPairSlices
open _root_.ThreeSum.SourceBandPairSlices


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData









theorem histogram_end {base n g m zero i bound : ℕ}
    (hb : _root_.ThreeSum.SourceBandLayout.work base n g m ≤ bound) (hz : zero+m ≤ bound) :
    _root_.ThreeSum.SourceBandPairSlices.histogramPtr base n g m zero i+m ≤ bound := by
  unfold _root_.ThreeSum.SourceBandPairSlices.histogramPtr
  split_ifs with hi
  · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_work (base := base) (m := m) hi
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes at hh
    omega
  · exact hz

theorem left_end (base NL NR g m i : ℕ) :
    _root_.ThreeSum.SourceBandPairSlices.histLeft base NL NR g m i+m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered base NL NR g m
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.histogram_end (by change _root_.ThreeSum.SourceBandPairData.rightBase base NL g m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m; omega)
    (by unfold _root_.ThreeSum.SourceBandPairData.next; omega)

theorem right_end (base NL NR g m i : ℕ) :
    _root_.ThreeSum.SourceBandPairSlices.histRight base NL NR g m i+m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.histogram_end (by change _root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m ≤ _root_.ThreeSum.SourceBandPairData.next base NL NR g m; unfold _root_.ThreeSum.SourceBandPairData.next; omega)
    (by unfold _root_.ThreeSum.SourceBandPairData.next; omega)





theorem heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g p m : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR base NL NR g p m shift) :
    μ base=(_root_.ThreeSum.SourceBandPairData.leftBase base : ℤ) ∧ μ (base+1)=(_root_.ThreeSum.BandPartition.size NL g : ℤ) ∧
    μ (base+2)=(_root_.ThreeSum.SourceBandPairData.rightBase base NL g m : ℤ) ∧ μ (base+3)=(_root_.ThreeSum.BandPartition.size NR g : ℤ) ∧
    μ (base+4)=(_root_.ThreeSum.SourceBandPairData.zeroBase base NL NR g m : ℤ) ∧ μ (base+5)=(_root_.ThreeSum.SourceBandPairData.next base NL NR g m : ℤ) ∧
    μ (base+6)=(NL : ℤ) ∧ μ (base+7)=(NR : ℤ) := by
  exact ⟨by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 0) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 1) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 2) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 3) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 4) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 5) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 6) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0,
    by simpa [_root_.ThreeSum.SourceBandPairData.header] using H.heads.getD (i := 7) (by simp [_root_.ThreeSum.SourceBandPairData.header]) 0⟩

end ThreeSum.SourceBandPairSlices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Actual constant-time retained histogram selection with empty padding -/

namespace ThreeSum.LightSourceBandHistSelect
open _root_.ThreeSum.LightSourceBandHistSelect


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairSlices
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices

set_option maxHeartbeats 2500000
set_option maxRecDepth 12000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem finish_ends {μ : ℕ → ℤ} {pair i dst left right : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : dst+2 ≤ lim.space)
    (hl : left ≤ lim.space) (hr : right ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.finishBody ⟨_root_.Light.frame [pair,i,dst,left,right],μ⟩ 40
      (fun σ => σ.mem dst=(left : ℤ) ∧ σ.mem (dst+1)=(right : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ σ.mem dst) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.finishBody
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (left : ℕ) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (right : ℕ) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self _ _ _
  · intro a ha
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

theorem right_ends {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst left : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : _root_.ThreeSum.SourceBandPairData.next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) (hl : left ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.rightBody
      ⟨_root_.Light.frame [pair,i,dst,left,_root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m],μ⟩ 200
      (fun σ => σ.mem dst=(left : ℤ) ∧
        σ.mem (dst+1)=(_root_.ThreeSum.SourceBandPairSlices.histRight pair NL NR g m i : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ σ.mem dst) := by
  obtain ⟨hbaseL,hcountL,hbaseR,hcountR,hzero,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.heads_read H
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered pair NL NR g m
  have hcounts := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NR g
  have hcountWord : (_root_.ThreeSum.BandPartition.size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.BandPartition.size NR g ≤ NL+NR+i+6 by omega)).trans hwN
  have hindexWord : (i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : i ≤ NL+NR+i+6)).trans hwN
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hheadBound : pair+8 ≤ dst := by unfold _root_.ThreeSum.SourceBandPairData.leftBase at ho; omega
  have hzeroBound : _root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m ≤ lim.space := by omega
  have htarget := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.right_end pair NL NR g m i
  have haddr2 : ((pair : ℤ)+2).toNat=pair+2 := by omega
  have haddr3 : ((pair : ℤ)+3).toNat=pair+3 := by omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.rightBody
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((i : ℤ) < (_root_.ThreeSum.BandPartition.size NR g : ℤ)) (fun hy => ?_) (fun hn => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountR, haddr3]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcountR, haddr3] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountR, haddr3] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have hi : i < _root_.ThreeSum.BandPartition.size NR g := by omega
    have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.header_end (base := _root_.ThreeSum.SourceBandPairData.rightBase pair NL g m) (m := m) hi
    have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_work (base := _root_.ThreeSum.SourceBandPairData.rightBase pair NL g m) (m := m) hi
    change _root_.ThreeSum.SourceBandLayout.flat (_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m) NR g m i+_root_.ThreeSum.SourceBandLayout.cap NR g ≤
      _root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m at hend
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes at hend
    have haddr : ((_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m : ℤ)+6*(i : ℤ)+3).toNat=_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m+6*i+3 := by omega
    have haddrWord : (_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m : ℤ)+6*(i : ℤ)+3 < lim.space := by exact_mod_cast (by omega : rightBase pair NL g m+6*i+3 < lim.space)
    have hprod : (6 : ℤ)*(i : ℤ) ≤ lim.word := by omega
    have hread := (H.right i hi).headHist
    have he : _root_.ThreeSum.SourceBandPairSlices.histRight pair NL NR g m i=_root_.ThreeSum.SourceBandLayout.hist (_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m) NR g m i := by
      simp only [_root_.ThreeSum.SourceBandPairSlices.histRight,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_pos hi]
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.hist (_root_.ThreeSum.SourceBandPairData.rightBase pair NL g m) NR g m i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbaseR, haddr2, haddr, hread]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hbaseR, haddr2, haddr, hread] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbaseR, haddr2, haddr, hread] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    rw [he]
    (focus
       (refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.finish_ends hw hs hl (by omega)) (fun _ p2m_macro_9485626418234881578 => p2m_macro_9485626418234881578) ?_;
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
                 | (ring_nf; omega))))
  · have hi : ¬ i < _root_.ThreeSum.BandPartition.size NR g := by omega
    have he : _root_.ThreeSum.SourceBandPairSlices.histRight pair NL NR g m i=_root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m := by
      simp only [_root_.ThreeSum.SourceBandPairSlices.histRight,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_neg hi]
    rw [he]
    (focus
       (refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.finish_ends hw hs hl hzeroBound) (fun _ p2m_macro_5848849775758747573 => p2m_macro_5848849775758747573) ?_;
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
                 | (ring_nf; omega))))





end ThreeSum.LightSourceBandHistSelect

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.SourceBandPairData
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData
open _root_.ThreeSum.SourceBandPairSlices
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets__implementation_0db1f2d778 {pMain : ℕ} (hmain : P[pMain]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.body)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst : ℕ} {shift : ℤ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : _root_.ThreeSum.SourceBandPairData.next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [pair,i,dst] μ 400
      (fun _ ν => ν dst=(_root_.ThreeSum.SourceBandPairSlices.histLeft pair NL NR g m i : ℤ) ∧
        ν (dst+1)=(_root_.ThreeSum.SourceBandPairSlices.histRight pair NL NR g m i : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  obtain ⟨hbaseL,hcountL,hbaseR,hcountR,hzero,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.heads_read H
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairData.ordered pair NL NR g m
  have hcounts := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le NL g
  have hcountWord : (_root_.ThreeSum.BandPartition.size NL g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _root_.ThreeSum.BandPartition.size NL g ≤ NL+NR+i+6 by omega)).trans hwN
  have hindexWord : (i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : i ≤ NL+NR+i+6)).trans hwN
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hheadBound : pair+8 ≤ dst := by unfold _root_.ThreeSum.SourceBandPairData.leftBase at ho; omega
  have hzeroBound : _root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m ≤ lim.space := by omega
  have htarget := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandPairSlices.left_end pair NL NR g m i
  have haddr1 : ((pair : ℤ)+1).toNat=pair+1 := by omega
  have haddr4 : ((pair : ℤ)+4).toNat=pair+4 := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.body
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hzero, haddr4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hzero, haddr4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hzero, haddr4] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hzero, haddr4]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hzero, haddr4] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hzero, haddr4] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((i : ℤ) < (_root_.ThreeSum.BandPartition.size NL g : ℤ)) (fun hy => ?_) (fun hn => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcountL, haddr1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcountL, haddr1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcountL, haddr1] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have hi : i < _root_.ThreeSum.BandPartition.size NL g := by omega
    have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.header_end (base := _root_.ThreeSum.SourceBandPairData.leftBase pair) (m := m) hi
    have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBandLayout.flat_end_le_work (base := _root_.ThreeSum.SourceBandPairData.leftBase pair) (m := m) hi
    change _root_.ThreeSum.SourceBandLayout.flat (_root_.ThreeSum.SourceBandPairData.leftBase pair) NL g m i+_root_.ThreeSum.SourceBandLayout.cap NL g ≤
      _root_.ThreeSum.SourceBandPairData.rightBase pair NL g m at hend
    unfold _root_.ThreeSum.SourceBandLayout.flat _root_.ThreeSum.SourceBandLayout.cursor _root_.ThreeSum.SourceBandLayout.offsets _root_.ThreeSum.SourceBandLayout.codes at hend
    have haddr : ((_root_.ThreeSum.SourceBandPairData.leftBase pair : ℤ)+6*(i : ℤ)+3).toNat=_root_.ThreeSum.SourceBandPairData.leftBase pair+6*i+3 := by omega
    have haddrWord : (_root_.ThreeSum.SourceBandPairData.leftBase pair : ℤ)+6*(i : ℤ)+3 < lim.space := by exact_mod_cast (by omega : leftBase pair+6*i+3 < lim.space)
    have hprod : (6 : ℤ)*(i : ℤ) ≤ lim.word := by omega
    have hread := (H.left i hi).headHist
    have he : _root_.ThreeSum.SourceBandPairSlices.histLeft pair NL NR g m i=_root_.ThreeSum.SourceBandLayout.hist (_root_.ThreeSum.SourceBandPairData.leftBase pair) NL g m i := by
      simp only [_root_.ThreeSum.SourceBandPairSlices.histLeft,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_pos hi]
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SourceBandLayout.hist (_root_.ThreeSum.SourceBandPairData.leftBase pair) NL g m i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbaseL, haddr, hread]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hbaseL, haddr, hread] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbaseL, haddr, hread] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    rw [he]
    (focus
       (refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.right_ends H hw hm hb hs hwN (by omega)) (fun _ p2m_macro_4647587060825134095 => p2m_macro_4647587060825134095) ?_;
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
                 | (ring_nf; omega))))
  · have hi : ¬ i < _root_.ThreeSum.BandPartition.size NL g := by omega
    have he : _root_.ThreeSum.SourceBandPairSlices.histLeft pair NL NR g m i=_root_.ThreeSum.SourceBandPairData.zeroBase pair NL NR g m := by
      simp only [_root_.ThreeSum.SourceBandPairSlices.histLeft,_root_.ThreeSum.SourceBandPairSlices.histogramPtr,if_neg hi]
    rw [he]
    (focus
       (refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.right_ends H hw hm hb hs hwN hzeroBound) (fun _ p2m_macro_2932398066432424556 => p2m_macro_2932398066432424556) ?_;
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
                 | (ring_nf; omega))))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets__implementation_0db1f2d778) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceBandHistSelect.meets__implementation_0db1f2d778)

#print axioms solution
