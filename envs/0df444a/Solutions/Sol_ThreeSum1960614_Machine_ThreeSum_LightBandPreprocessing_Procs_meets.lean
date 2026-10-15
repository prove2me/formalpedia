-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:56:23.022223+00:00
-- url     : https://prove2.me/submissions/c957aa82-4eb8-4995-844d-1cc15d5193f1

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Theorems.Thm_ThreeSum_LightBandPreprocessing_Represents_keep
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightHeaderBands_Procs_meets
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_transfer
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSortedBands_Procs_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.LightBandEnumeration
end ThreeSum.LightBandEnumeration
namespace ThreeSum.LightBandPreprocessing
end ThreeSum.LightBandPreprocessing
namespace ThreeSum.LightSortedBands
end ThreeSum.LightSortedBands
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
end ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
end ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing
namespace ThreeSum1960614.Machine.ThreeSum.LightSortedBands
end ThreeSum1960614.Machine.ThreeSum.LightSortedBands
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

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

theorem size_mono {n m g : ℕ} (h : n ≤ m) : _root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.BandPartition.size m g := by
  by_cases hn : n = 0
  · simp [_root_.ThreeSum.BandPartition.size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [_root_.ThreeSum.BandPartition.size,if_neg hn,if_neg hm]
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

namespace ThreeSum1960614.Machine

/-!
# A closed machine program listing all relevant sorted-band candidates

The program computes its own binary width and power table, then executes
exactly the three rectangular owner tables. Every table cell contains an
interval lookup result (index plus one, zero for a miss). The source arrays
remain intact. The coverage theorem below connects these actual memory cells
to every relevant triple, and hence to every exact equation in the bands.
-/

namespace ThreeSum.LightBandEnumeration
open _root_.ThreeSum.LightBandEnumeration


set_option maxHeartbeats 1200000
set_option maxRecDepth 4000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}












































theorem count_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.count a b c ≤ _root_.ThreeSum.LightBandEnumeration.count a' b' c' := by
  unfold _root_.ThreeSum.LightBandEnumeration.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul hb hc) (Nat.mul_le_mul ha hb))
    (Nat.mul_le_mul ha hc)

theorem width_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.width a b c ≤ _root_.ThreeSum.LightBandEnumeration.width a' b' c' := Nat.clog_mono_right 2 (by omega)

theorem time_mono {a b c a' b' c' : ℕ} (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    _root_.ThreeSum.LightBandEnumeration.time a b c ≤ _root_.ThreeSum.LightBandEnumeration.time a' b' c' := by
  have hw := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.width_mono ha hb hc
  have hlog := Nat.clog_mono_right 2 (show a+b+c+1 ≤ a'+b'+c'+1 by omega)
  unfold _root_.ThreeSum.LightBandEnumeration.time _root_.Light.clog2Time _root_.Light.powTableTime _root_.ThreeSum.LightBandTable.time _root_.ThreeSum.LightBandTable.rowTime
    _root_.ThreeSum.LightBandLookup.time _root_.ThreeSum.LightBandLookup.searchTime
  gcongr

end ThreeSum.LightBandEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Normalizing one color class and constructing all its band endpoints

This closed eleven-procedure program joins the actual merge sort, adjacent
deduplication, quotient computation, and endpoint passes. It writes the
distinct-value length and band count in a two-cell header. The following
cells are the lower endpoints and, after the distinct-value length, the
upper endpoints. The membership witness still refers to the original class.
-/

namespace ThreeSum.LightSortedBands
open _root_.ThreeSum.LightSortedBands


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}




















/-- The constructed endpoint arrays directly instantiate the exact family
interface of the owner-listing machine. -/
theorem Prepared.family {μ : ℕ → ℤ} {values endpoints g : ℕ} {original : List ℤ}
    (h : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ values endpoints g original) (hg : 0 < g) :
    ∃ (L : List ℤ) (hs : L.Pairwise (· < ·)),
      _root_.ThreeSum1960614.Machine.Light.Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
      μ endpoints = (L.length : ℤ) ∧
      μ (endpoints+1) = (_root_.ThreeSum.BandPartition.family (fun i => L.getD i 0) L.length g hg
        (_root_.ThreeSum.LightSortedBands.getD_strict hs)).size ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.At μ (endpoints+2) (endpoints+2+L.length)
        (_root_.ThreeSum.BandPartition.family (fun i => L.getD i 0) L.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hs)) := by
  obtain ⟨L,hL,hs,hn,hmem,hlen,hcount,hlo,hhi⟩ := h
  exact ⟨L,hs,hL,hn,hmem,hlen,hcount,hlo,hhi⟩





theorem family_bounded {L original : List ℤ} {g U : ℕ} (hg : 0 < g)
    (hs : L.Pairwise (· < ·)) (hmem : ∀ z, z ∈ L ↔ z ∈ original)
    (hU : ∀ z ∈ original, |z| ≤ (U : ℤ)) :
    _root_.ThreeSum.LightBandEnumeration.Bounded
      (_root_.ThreeSum.BandPartition.family (fun i => L.getD i 0) L.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hs)) U := by
  have hget (i : ℕ) (hi : i < L.length) : |L.getD i 0| ≤ (U : ℤ) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact hU _ ((hmem _).mp (List.getElem_mem hi))
  intro i hi
  exact ⟨hget _ (_root_.ThreeSum.BandPartition.start_lt hg hi),hget _ (_root_.ThreeSum.BandPartition.stop_sub_one_lt hg hi)⟩





end ThreeSum.LightSortedBands

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandPreprocessing
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets__implementation_1f1fd0c61d {pMain srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ} (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : _root_.ThreeSum.LightBandPreprocessing.space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandPreprocessing.word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.LightBandPreprocessing.depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcA originalA) (hBread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcB originalB) (hCread : _root_.ThreeSum1960614.Machine.Light.Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (_root_.ThreeSum.LightBandPreprocessing.time originalA.length originalB.length originalC.length g)
      (fun r μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcA) := by
  have hspace' : work+(originalA.length+originalB.length+originalC.length)+
      _root_.ThreeSum.LightBandEnumeration.count (_root_.ThreeSum.BandPartition.size originalA.length g) (_root_.ThreeSum.BandPartition.size originalB.length g) (_root_.ThreeSum.BandPartition.size originalC.length g)+
      _root_.ThreeSum.LightBandEnumeration.width (_root_.ThreeSum.BandPartition.size originalA.length g) (_root_.ThreeSum.BandPartition.size originalB.length g) (_root_.ThreeSum.BandPartition.size originalC.length g)+1 ≤
      lim.space := hspace
  have hnormSpaceA : _root_.ThreeSum.LightSortedBands.space work originalA.length ≤ lim.space := by
    unfold _root_.ThreeSum.LightSortedBands.space; omega
  have hnormSpaceB : _root_.ThreeSum.LightSortedBands.space work originalB.length ≤ lim.space := by
    unfold _root_.ThreeSum.LightSortedBands.space; omega
  have hnormSpaceC : _root_.ThreeSum.LightSortedBands.space work originalC.length ≤ lim.space := by
    unfold _root_.ThreeSum.LightSortedBands.space; omega
  have hnormWord (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      ((n+g+2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : n+g+2 ≤ _root_.ThreeSum.LightBandPreprocessing.word originalA.length originalB.length originalC.length g U := by unfold _root_.ThreeSum.LightBandPreprocessing.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnormDepth (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      (d+1)+n+Nat.clog 2 n+3 ≤ lim.depth := by
    have hlog := Nat.clog_mono_right 2 hn
    unfold _root_.ThreeSum.LightBandPreprocessing.depth at hd
    omega
  have hgWord : ((g+2 : ℕ) : ℤ) ≤ lim.word := by simpa using hnormWord 0 (by omega)
  have hdSmall : d+4 ≤ lim.depth := by unfold _root_.ThreeSum.LightBandPreprocessing.depth at hd; omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.body _root_.ThreeSum.LightBandPreprocessing.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.prepare.meets (d := d + 1) (src := srcA) (values := av) (endpoints := ae) (work := work) hw hg (by omega) hav (by omega) hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hAread) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.prepare.meets (d := d + 1) (src := srcA) (values := av) (endpoints := ae) (work := work) hw hg (by omega) hav (by omega) hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hAread) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
     on_goal -1 => (rintro aCount μ₁ ⟨haCount, hPreparedA, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hBread₁ : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ srcB originalB := by
    intro i hi
    rw [hkeep₁ (srcB+i) (by omega) (by omega) (by omega) (by omega)]
    exact hBread i hi
  have hCread₁ : _root_.ThreeSum1960614.Machine.Light.Seg μ₁ srcC originalC := by
    intro i hi
    rw [hkeep₁ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.prepare.meets (d := d + 1) (src := srcB) (values := bv) (endpoints := be) (work := work) hw hg (by omega) hbv (by omega) hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hBread₁) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.prepare.meets (d := d + 1) (src := srcB) (values := bv) (endpoints := be) (work := work) hw hg (by omega) hbv (by omega) hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hBread₁) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
     on_goal -1 => (rintro bCount μ₂ ⟨hbCount, hPreparedB, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hPreparedA₂ : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ₂ av ae g originalA := by
    apply _root_.ThreeSum.LightSortedBands.Prepared.transfer hPreparedA
    intro a ha
    apply hkeep₂ a <;> rcases ha with ha | ha <;> omega
  have hCread₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ srcC originalC := by
    intro i hi
    rw [hkeep₂ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread₁ i hi
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.prepare.meets (d := d + 1) (src := srcC) (values := cv) (endpoints := ce) (work := work) hw hg (by omega) hcv hce hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hCread₂) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (R.prepare.meets (d := d + 1) (src := srcC) (values := cv) (endpoints := ce) (work := work) hw hg (by omega) hcv hce hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hCread₂) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
     on_goal -1 => (rintro cCount μ₃ ⟨hcCount, hPreparedC, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hPreparedA₃ : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ₃ av ae g originalA := by
    apply _root_.ThreeSum.LightSortedBands.Prepared.transfer hPreparedA₂
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  have hPreparedB₃ : _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared μ₃ bv be g originalB := by
    apply _root_.ThreeSum.LightSortedBands.Prepared.transfer hPreparedB
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  obtain ⟨A,hsA,hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared.family hPreparedA₃ hg
  obtain ⟨B,hsB,hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared.family hPreparedB₃ hg
  obtain ⟨C,hsC,hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.Prepared.family hPreparedC hg
  let aFamily := _root_.ThreeSum.BandPartition.family (fun i => A.getD i 0) A.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsA)
  let bFamily := _root_.ThreeSum.BandPartition.family (fun i => B.getD i 0) B.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsB)
  let cFamily := _root_.ThreeSum.BandPartition.family (fun i => C.getD i 0) C.length g hg (_root_.ThreeSum.LightSortedBands.getD_strict hsC)
  have hsa : aFamily.size ≤ _root_.ThreeSum.BandPartition.size originalA.length g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hALen
  have hsb : bFamily.size ≤ _root_.ThreeSum.BandPartition.size originalB.length g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hBLen
  have hsc : cFamily.size ≤ _root_.ThreeSum.BandPartition.size originalC.length g := _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_mono hCLen
  have hsan : aFamily.size ≤ originalA.length := hsa.trans (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le _ _)
  have hsbn : bFamily.size ≤ originalB.length := hsb.trans (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le _ _)
  have hscn : cFamily.size ≤ originalC.length := hsc.trans (_root_.ThreeSum1960614.Machine.ThreeSum.BandPartition.size_le _ _)
  have hcountBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.count_mono hsa hsb hsc
  have hwidthBound := _root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.width_mono hsa hsb hsc
  have henumSpace : _root_.ThreeSum.LightBandEnumeration.space work aFamily.size bFamily.size cFamily.size ≤ lim.space := by
    unfold _root_.ThreeSum.LightBandEnumeration.space
    omega
  have henumWord : (_root_.ThreeSum.LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U ≤
        _root_.ThreeSum.LightBandPreprocessing.word originalA.length originalB.length originalC.length g U := by
      unfold _root_.ThreeSum.LightBandPreprocessing.word _root_.ThreeSum.LightBandEnumeration.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have henumDepth : (d+1)+_root_.ThreeSum.LightBandEnumeration.width aFamily.size bFamily.size cFamily.size+5 ≤ lim.depth := by
    unfold _root_.ThreeSum.LightBandPreprocessing.depth at hd
    omega
  have henumTime : _root_.ThreeSum.LightHeaderBands.time aFamily.size bFamily.size cFamily.size ≤
      _root_.ThreeSum.LightHeaderBands.time (_root_.ThreeSum.BandPartition.size originalA.length g) (_root_.ThreeSum.BandPartition.size originalB.length g) (_root_.ThreeSum.BandPartition.size originalC.length g) :=
    Nat.add_le_add_right (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandEnumeration.time_mono hsa hsb hsc) 100
  have hrepA : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ₃ av ae g hg originalA A hsA :=
    ⟨hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩
  have hrepB : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ₃ bv be g hg originalB B hsB :=
    ⟨hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩
  have hrepC : _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Represents μ₃ cv ce g hg originalC C hsC :=
    ⟨hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw (by omega) (by omega) (by omega) henumSpace henumWord henumDepth hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsA hAMem hAU) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsB hBMem hBU) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time henumTime) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw (by omega) (by omega) (by omega) henumSpace henumWord henumDepth hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsA hAMem hAU) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsB hBMem hBU) (_root_.ThreeSum1960614.Machine.ThreeSum.LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time henumTime) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSortedBands.time, _root_.ThreeSum.LightNormalize.time, _root_.Light.sortTime, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
     on_goal -1 => (rintro result μ₄ ⟨hresult, htable, hkeep₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsA) hrepA hkeep₄ (by omega) (by omega),
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsB) hrepB hkeep₄ (by omega) (by omega),
    _root_.ThreeSum.LightBandPreprocessing.Represents.keep (hs := hsC) hrepC hkeep₄ (by omega) hce,htable⟩,?_⟩
  intro a ha
  change μ₄ a = μ a
  rw [hkeep₄ a (by omega),hkeep₃ a (by omega) (by omega) (by omega) (by omega),
    hkeep₂ a (by omega) (by omega) (by omega) (by omega),
    hkeep₁ a (by omega) (by omega) (by omega) (by omega)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets__implementation_1f1fd0c61d) := (@ThreeSum1960614.Machine.ThreeSum.LightBandPreprocessing.Procs.meets__implementation_1f1fd0c61d)

#print axioms solution
