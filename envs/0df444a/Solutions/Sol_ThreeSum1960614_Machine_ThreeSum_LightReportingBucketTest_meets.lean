-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:07:06.79934+00:00
-- url     : https://prove2.me/submissions/947b703f-f965-4186-acf5-b3cdec4f1673

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.Nat.Choose.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingBucketPairs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketSelect_meets
import Theorems.Thm_ThreeSum_SourceBuckets_position_bucket_iff
import Theorems.Thm_ThreeSum_SourceBuckets_position_injective

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightReportingBucketTest
end ThreeSum.LightReportingBucketTest
namespace ThreeSum.LightSourceBucketSelect
end ThreeSum.LightSourceBucketSelect
namespace ThreeSum.ReportingHostBucketTest
end ThreeSum.ReportingHostBucketTest
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
end ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
end ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
end ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
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







theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    _root_.ThreeSum.LightHistogram.count key r (i + 1) = _root_.ThreeSum.LightHistogram.count key r i + if key i = r then 1 else 0 := by
  unfold _root_.ThreeSum.LightHistogram.count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]













end ThreeSum.LightHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets
open _root_.ThreeSum.SourceBuckets


open _root_.Finset
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000





theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    _root_.ThreeSum.SourceBuckets.offset key N (r+1) = _root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightHistogram.count key r N := by
  exact Finset.sum_range_succ _ _

theorem offset_mono (key : ℕ → ℕ) (N : ℕ) : Monotone (_root_.ThreeSum.SourceBuckets.offset key N) := by
  intro r s hrs
  exact Finset.sum_le_sum_of_subset (Finset.range_mono hrs)

theorem count_mono (key : ℕ → ℕ) (r : ℕ) : Monotone (_root_.ThreeSum.LightHistogram.count key r) := by
  intro i j hij
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono hij))

theorem count_strict {key : ℕ → ℕ} {r i j : ℕ} (hij : i < j) (hkey : key i = r) :
    _root_.ThreeSum.LightHistogram.count key r i < _root_.ThreeSum.LightHistogram.count key r j := by
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram.count_succ key r i
  simp only [hkey,ite_true] at he
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_mono key r (show i+1 ≤ j by omega)
  omega

theorem offset_total {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M) :
    _root_.ThreeSum.SourceBuckets.offset key N M = N := by
  unfold _root_.ThreeSum.SourceBuckets.offset _root_.ThreeSum.LightHistogram.count
  have he := Finset.card_eq_sum_card_fiberwise
    (f := key) (s := range N) (t := range M)
    (fun i hi => Finset.mem_range.mpr (hkey i (Finset.mem_range.mp hi)))
  simpa only [Finset.card_range] using he.symm

theorem offset_le {key : ℕ → ℕ} {N M r : ℕ} (hkey : ∀ i < N, key i < M) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBuckets.offset key N r ≤ N := by
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_mono key N hr).trans_eq (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_total hkey)





theorem position_end {key : ℕ → ℕ} {N i : ℕ} (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < _root_.ThreeSum.SourceBuckets.offset key N (key i+1) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  exact Nat.add_lt_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.count_strict hi rfl) _

theorem position_lt {key : ℕ → ℕ} {N M i : ℕ} (hkey : ∀ i < N, key i < M) (hi : i < N) :
    _root_.ThreeSum.SourceBuckets.position key N i < N :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_end hi).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (by have hk := hkey i hi; omega))







theorem exists_position {key : ℕ → ℕ} {N M : ℕ} (hkey : ∀ i < N, key i < M)
    {t : ℕ} (ht : t < N) : ∃ i < N, _root_.ThreeSum.SourceBuckets.position key N i = t := by
  let f : Fin N → Fin N := fun i => ⟨_root_.ThreeSum.SourceBuckets.position key N i.val,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_lt hkey i.isLt⟩
  have hf : Function.Injective f := by
    intro i j he
    exact Fin.ext (_root_.ThreeSum.SourceBuckets.position_injective i.isLt j.isLt (congrArg Fin.val he))
  obtain ⟨i,hi⟩ := Finite.surjective_of_injective hf ⟨t,ht⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

theorem exists_bucket_position {key : ℕ → ℕ} {N M r t : ℕ}
    (hkey : ∀ i < N, key i < M) (hr : r < M) (ht : t < _root_.ThreeSum.LightHistogram.count key r N) :
    ∃ i < N, key i = r ∧ _root_.ThreeSum.SourceBuckets.position key N i = _root_.ThreeSum.SourceBuckets.offset key N r+t := by
  have htN : _root_.ThreeSum.SourceBuckets.offset key N r+t < N := by
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (show r+1 ≤ M by omega)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ] at he
    omega
  obtain ⟨i,hi,he⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.exists_position hkey htN
  refine ⟨i,hi,?_,he⟩
  apply (_root_.ThreeSum.SourceBuckets.position_bucket_iff hi).mp
  rw [he,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  omega







theorem Stored.read_bucket {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r t : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M)
    (hr : r < M) (ht : t < _root_.ThreeSum.LightHistogram.count key r N) :
    ∃ i < N, key i = r ∧ _root_.ThreeSum.SourceBuckets.position key N i = _root_.ThreeSum.SourceBuckets.offset key N r+t ∧
      μ (flat+_root_.ThreeSum.SourceBuckets.offset key N r+t) = (i : ℤ) := by
  obtain ⟨i,hi,hki,hpos⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.exists_bucket_position hkey hr ht
  refine ⟨i,hi,hki,hpos,?_⟩
  simpa only [hpos,Nat.add_assoc] using H.indices i hi







end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Physical bucket-test semantics and original-index completeness

The selected offset segment contains exactly the original physical indices
in one residue fiber, with an independent endpoint flag. The literal pair
tester therefore recognizes exactly the compatible original value pairs.
-/

namespace ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum.ReportingHostBucketTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



theorem selected_le (key : ℕ → ℕ) (N r flag : ℕ) :
    _root_.ThreeSum.LightSourceBucketSelect.countSelected key N r flag ≤ _root_.ThreeSum.LightHistogram.count key r N := by
  unfold _root_.ThreeSum.LightSourceBucketSelect.countSelected
  split <;> omega

theorem selected_end {key : ℕ → ℕ} {N M r flag : ℕ}
    (hkey : ∀ i < N, key i<M) (hr : r<M) :
    _root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightSourceBucketSelect.countSelected key N r flag ≤ N := by
  have hend := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_le hkey (show r+1 ≤ M by omega)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ] at hend
  exact (Nat.add_le_add_left (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_le key N r flag) _).trans hend

theorem selected_read {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag j : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hkey : ∀ i < N, key i<M)
    (hr : r<M) (hj : j<_root_.ThreeSum.LightSourceBucketSelect.countSelected key N r flag) :
    _root_.ThreeSum.ReportingHostBucketTest.index μ flat key N r j<N ∧
      μ (flat+_root_.ThreeSum.SourceBuckets.offset key N r+j)=(_root_.ThreeSum.ReportingHostBucketTest.index μ flat key N r j : ℤ) := by
  obtain ⟨i,hi,_,_,hread⟩ := H.read_bucket hkey hr (hj.trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_le key N r flag))
  simp only [_root_.ThreeSum.ReportingHostBucketTest.index,hread,Int.toNat_natCast]
  exact ⟨hi,trivial⟩









end ThreeSum.ReportingHostBucketTest

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect
open _root_.ThreeSum.ReportingHostBucketTest
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets__implementation_fe5a6d6c58 {pMain pSelect pPairs pRow srcL srcR offsetsL offsetsR flatL flatR NL NR M rL rR flagL flagR work : ℕ}
    {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.body pSelect pPairs))
    (hselect : P[pSelect]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.body)
    (hpairs : P[pPairs]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.body pRow))
    (hrow : P[pRow]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (keyL keyR : ℕ → ℕ)
    (HL : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyL NL M offsetsL flatL) (HR : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ keyR NR M offsetsR flatR)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hsrcL : srcL+NL ≤ work) (hsrcR : srcR+NR ≤ work)
    (hoffsetsL : offsetsL+M+1 ≤ work) (hoffsetsR : offsetsR+M+1 ≤ work)
    (hflatL : flatL+NL ≤ work) (hflatR : flatR+NR ≤ work) (hspace : work+4 ≤ lim.space)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (hflagL : flagL≤1) (hflagR : flagR≤1)
    (hreadL : ∀ i < NL, μ (srcL+i)=left i) (hreadR : ∀ j < NR, μ (srcR+j)=right j)
    (hvaluesL : ∀ i < NL, |left i|≤lim.word) (hvaluesR : ∀ j < NR, |right j|≤lim.word)
    (ha : |a|≤lim.word) (htarget : ∀ i < NL, |a+left i|≤lim.word)
    (hcountWord : ((NL*NR : ℕ) : ℤ)≤lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,srcL,srcR,offsetsL,flatL,rL,flagL,offsetsR,flatR,rR,flagR,NL,NR,M,work]
      μ (_root_.ThreeSum.LightReportingBucketTest.time keyL keyR NL NR rL rR flagL flagR)
      (fun r ν => r=(_root_.ThreeSum.ReportingHostBucketTest.testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν work 4) := by
  let startL := _root_.ThreeSum.SourceBuckets.offset keyL NL rL
  let startR := _root_.ThreeSum.SourceBuckets.offset keyR NR rR
  let nL := _root_.ThreeSum.LightSourceBucketSelect.countSelected keyL NL rL flagL
  let nR := _root_.ThreeSum.LightSourceBucketSelect.countSelected keyR NR rR flagR
  have hendL : startL+nL≤NL := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_end hkeyL hrL
  have hendR : startR+nR≤NR := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_end hkeyR hrR
  have haBounds := abs_le.mp ha
  have hselectedWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul (by omega) (by omega))).trans hcountWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.body _root_.ThreeSum.LightReportingBucketTest.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets (d := d + 1) hselect HL hw hoffsetsL hflatL (by omega) hkeyL hrL hflagL) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets (d := d + 1) hselect HL hw hoffsetsL hflatL (by omega) hkeyL hrL hflagL) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     on_goal -1 => (rintro unused μ₁ ⟨hptrL, hlenL, hkeepL⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have HR₁ : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ₁ keyR NR M offsetsR flatR := by
    constructor
    · intro r hr
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.offsets r hr)
    · intro i hi
      have hpos := _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.position_lt hkeyR hi
      exact (hkeepL _ (Or.inl (by omega))).trans (HR.indices i hi)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets (d := d + 1) (dst := work + 2) hselect HR₁ hw (by omega) (by omega) (by omega) hkeyR hrR hflagR) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSelect.meets (d := d + 1) (dst := work + 2) hselect HR₁ hw (by omega) (by omega) (by omega) hkeyR hrR hflagR) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     on_goal -1 => (rintro unused μ₂ ⟨hptrR, hlenR, hkeepR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepBelow (i : ℕ) (hi : i<work) : μ₂ i=μ i :=
    (hkeepR i (Or.inl (by omega))).trans (hkeepL i (Or.inl hi))
  have hptrL' : μ₂ work=((flatL+startL : ℕ) : ℤ) :=
    (hkeepR work (Or.inl (by omega))).trans hptrL
  have hlenL' : μ₂ (work+1)=(nL : ℤ) :=
    (hkeepR (work+1) (Or.inl (by omega))).trans hlenL
  change μ₂ (work+2)=((flatR+startR : ℕ) : ℤ) at hptrR
  change μ₂ (work+2+1)=(nR : ℤ) at hlenR
  have hlenR' : μ₂ (work+3)=(nR : ℤ) := by simpa only [Nat.add_assoc] using hlenR
  have hptrRZ : μ₂ (((work : ℤ)+2).toNat)=((flatR+startR : ℕ) : ℤ) := by
    rw [show ((work : ℤ)+2).toNat=work+2 by omega]
    exact hptrR
  have hlenRZ : μ₂ (((work : ℤ)+3).toNat)=(nR : ℤ) := by
    rw [show ((work : ℤ)+3).toNat=work+3 by omega]
    exact hlenR'
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (flatL + startL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptrL', _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptrL', _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptrL', _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (nL : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlenL', _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlenL', _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlenL', _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (flatR + startR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hptrRZ, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hptrRZ, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hptrRZ, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (nR : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlenRZ, _root_.ThreeSum.LightReportingBucketPairs.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hlenRZ, _root_.ThreeSum.LightReportingBucketPairs.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlenRZ, _root_.ThreeSum.LightReportingBucketPairs.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hreadIL (i : ℕ) (hi : i<nL) :
      μ₂ (flatL+startL+i)=(_root_.ThreeSum.ReportingHostBucketTest.index μ flatL keyL NL rL i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_read HL hkeyL hrL hi).2
  have hreadIR (i : ℕ) (hi : i<nR) :
      μ₂ (flatR+startR+i)=(_root_.ThreeSum.ReportingHostBucketTest.index μ flatR keyR NR rR i : ℤ) :=
    (hkeepBelow _ (by omega)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_read HR hkeyR hrR hi).2
  have hrun := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingBucketPairs.meets (d := d+1) (μ := μ₂)
    (indicesL := flatL+startL) (indicesR := flatR+startR) hpairs hrow a left right
    (_root_.ThreeSum.ReportingHostBucketTest.index μ flatL keyL NL rL) (_root_.ThreeSum.ReportingHostBucketTest.index μ flatR keyR NR rR) hw (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (fun _ hi => (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_read HL hkeyL hrL hi).1)
    (fun _ hi => (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostBucketTest.selected_read HR hkeyR hrR hi).1) hreadIL hreadIR
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadL i hi))
    (fun i hi => (hkeepBelow _ (by omega)).trans (hreadR i hi))
    hvaluesL hvaluesR ha htarget hselectedWord
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingBucketPairs.time, startL, startR, nL, nR]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingBucketPairs.time, startL, startR, nL, nR] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingBucketPairs.time, startL, startR, nL, nR] <;> omega)
     on_goal -1 => (rintro found ν ⟨hfound, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst ν
  refine ⟨hfound,?_⟩
  intro i hi
  exact (hkeepR i (by rcases hi with hi | hi <;> omega)).trans
    (hkeepL i (by rcases hi with hi | hi <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets__implementation_fe5a6d6c58) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingBucketTest.meets__implementation_fe5a6d6c58)

#print axioms solution
