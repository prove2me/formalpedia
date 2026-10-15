-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:31:04.541972+00:00
-- url     : https://prove2.me/submissions/0ac06bee-2d6c-4aca-80af-dae718b308b6

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
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
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.TakeDrop
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
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBandWeightedScoreSlice_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightedScore_Procs_meets

private theorem platform_seg_cons_2bb4667b94 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

@[simp] private theorem platform_seg_nil_2bb4667b94 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandWeightedScore
end ThreeSum.BandWeightedScore
namespace ThreeSum.LightBandWeightedScoreCell
end ThreeSum.LightBandWeightedScoreCell
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
end ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
namespace ThreeSum1960614.Machine.ThreeSum.BandEnumeration
end ThreeSum1960614.Machine.ThreeSum.BandEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
end ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
namespace ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell
end ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)





































































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandCandidateRows


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.BandEnumeration

set_option maxHeartbeats 1300000















theorem record_fields {μ : ℕ → ℤ} {dst : ℕ} {r : _root_.ThreeSum.BandCandidateRows.Record}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ dst r.cells) :
    μ dst=(r.flag : ℤ) ∧ μ (dst+1)=(r.a : ℤ) ∧
      μ (dst+2)=(r.b : ℤ) ∧ μ (dst+3)=(r.c : ℤ) := by
  simpa [_root_.ThreeSum.BandCandidateRows.Record.cells,platform_seg_cons_2bb4667b94,Nat.add_assoc] using H

end ThreeSum.BandCandidateRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore
open _root_.ThreeSum.BandWeightedScore


open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.Finset
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000



theorem length_le (n g a : ℕ) : _root_.ThreeSum.BandWeightedScore.length n g a ≤ g := min_le_left _ _



theorem position_lt {n g a i : ℕ} (hi : i < _root_.ThreeSum.BandWeightedScore.length n g a) : a*g+i < n := by
  have hh := min_le_right g (n-a*g)
  unfold _root_.ThreeSum.BandWeightedScore.length at hi
  omega

theorem end_le {n g a : ℕ} (ha : a*g ≤ n) : a*g+_root_.ThreeSum.BandWeightedScore.length n g a ≤ n := by
  have hh := min_le_right g (n-a*g)
  unfold _root_.ThreeSum.BandWeightedScore.length
  omega

























end ThreeSum.BandWeightedScore

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute one flagged owner's weighted modular score

The actual record supplies its three band indices. This routine computes
their truncated lengths and invokes the existing exact counting program on
those slices. An unflagged record contributes zero without a counting call.
-/

namespace ThreeSum.LightBandWeightedScoreCell
open _root_.ThreeSum.LightBandWeightedScoreCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000







theorem score_time_le {nA nB nC g : ℕ} (maxMod s U : ℕ)
    (hA : nA ≤ g) (hB : nB ≤ g) (hC : nC ≤ g) :
    _root_.ThreeSum.LightWeightedScore.runtimeTime maxMod nA nB nC s U ≤
      _root_.ThreeSum.LightWeightedScore.runtimeTime maxMod g g g s U := by
  have hta := Nat.mul_le_mul_right (_root_.ThreeSum.LightResidues.residueBudget U+30) hA
  have htb := Nat.mul_le_mul_right (_root_.ThreeSum.LightResidues.residueBudget U+30) hB
  have htc := Nat.mul_le_mul_right (_root_.ThreeSum.LightResidues.residueBudget U+30) hC
  have hc : _root_.ThreeSum.LightModuloCounts.time maxMod nA nB nC U ≤ _root_.ThreeSum.LightModuloCounts.time maxMod g g g U := by
    unfold _root_.ThreeSum.LightModuloCounts.time _root_.ThreeSum.LightResidueHistogram.time _root_.ThreeSum.LightHistogram.histogramTime
      _root_.ThreeSum.LightHistogram.countTime _root_.ThreeSum.LightResidues.residuesTime _root_.ThreeSum.LightLookupSum.time
    omega
  have hs := Nat.mul_le_mul_left s (Nat.add_le_add_right
    (Nat.add_le_add_right hc (_root_.ThreeSum.LightWeightedScore.jointTime maxMod)) 100)
  unfold _root_.ThreeSum.LightWeightedScore.runtimeTime _root_.ThreeSum.LightWeightedScore.time
  omega

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}









end ThreeSum.LightBandWeightedScoreCell

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandWeightedScoreCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandCandidateRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows
open _root_.ThreeSum.BandWeightedScore
open _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.meets__implementation_01223db19d {pMain pLength pScore : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightWeightedScore.Procs P pScore)
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.body pLength pScore))
    (hlength : P[pLength]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.body)
    (primes : ℕ → ℕ) (r : _root_.ThreeSum.BandCandidateRows.Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrec : rec+4 ≤ free) (haux : aux+s ≤ free)
    (hspace : _root_.ThreeSum.LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBandWeightedScoreCell.word maxMod nA nB nC g s U : ℤ) ≤ lim.word)
    (hrecord : _root_.ThreeSum1960614.Machine.Light.Seg μ rec r.cells) (hflag : r.flag=0 ∨ r.flag=1)
    (hvalid : r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,b,c,nA,nB,nC,g,rec,q,aux,s,free] μ (_root_.ThreeSum.LightBandWeightedScoreCell.time maxMod g s U)
      (fun result ν => result=(_root_.ThreeSum.BandWeightedScore.block primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) r : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hbudget (k : ℕ) (hk : k ≤ _root_.ThreeSum.LightBandWeightedScoreCell.word maxMod nA nB nC g s U) : (k : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hk).trans hword
  have hscoreWord := hbudget (_root_.ThreeSum.LightWeightedScore.word maxMod g s U) (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have hlenAWord := hbudget (nA+g+4) (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have hlenBWord := hbudget (nB+g+4) (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have hlenCWord := hbudget (nC+g+4) (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have h1Word := hbudget 1 (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have hgWord := hbudget g (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
  have hflagLe : r.flag ≤ 1 := by rcases hflag with hh | hh <;> omega
  have hflagWord : (r.flag : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hflagLe).trans h1Word
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  obtain ⟨hfRead,haRead,hbRead,hcRead⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BandCandidateRows.record_fields hrecord
  have hrec1Addr : ((rec : ℤ)+1).toNat=rec+1 := by omega
  have hrec2Addr : ((rec : ℤ)+2).toNat=rec+2 := by omega
  have hrec3Addr : ((rec : ℤ)+3).toNat=rec+3 := by omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.body _root_.ThreeSum.LightBandWeightedScoreCell.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (r.flag : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfRead]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfRead] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfRead] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((r.flag : ℤ) = 1) (fun hf => ?_) (fun hf => ?_) ?_ ?_
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
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have hfNat : r.flag=1 := by omega
    obtain ⟨hstartA,hstartB,hstartC⟩ := hvalid hfNat
    have hAi : r.a ≤ nA := (Nat.le_mul_of_pos_right r.a hg).trans hstartA
    have hBi : r.b ≤ nB := (Nat.le_mul_of_pos_right r.b hg).trans hstartB
    have hCi : r.c ≤ nC := (Nat.le_mul_of_pos_right r.c hg).trans hstartC
    have hAiWord := hbudget r.a (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
    have hBiWord := hbudget r.b (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
    have hCiWord := hbudget r.c (by unfold _root_.ThreeSum.LightBandWeightedScoreCell.word; omega)
    have hApWord : (r.a : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.a*g ≤ lim.space by omega) : (r.a : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hBpWord : (r.b : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.b*g ≤ lim.space by omega) : (r.b : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hCpWord : (r.c : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.c*g ≤ lim.space by omega) : (r.c : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hApN : (0 : ℤ) ≤ (r.a : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hBpN : (0 : ℤ) ≤ (r.b : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hCpN : (0 : ℤ) ≤ (r.c : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hAend := _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.end_le (g := g) hstartA
    have hBend := _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.end_le (g := g) hstartB
    have hCend := _root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.end_le (g := g) hstartC
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (r.a : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, haRead, hrec1Addr]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [haRead, hrec1Addr] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, haRead, hrec1Addr] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (r.b : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbRead, hrec2Addr]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hbRead, hrec2Addr] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbRead, hrec2Addr] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (r.c : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcRead, hrec3Addr]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcRead, hrec3Addr] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcRead, hrec3Addr] <;> omega)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartA hlenAWord) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartA hlenAWord) ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro va μ₁ ⟨hva, hmemA⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₁
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartB hlenBWord) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartB hlenBWord) ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro vb μ₂ ⟨hvb, hmemB⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₂
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartC hlenCWord) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreSlice.meets (d := d + 1) hlength hg hstartC hlenCWord) ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro vc μ₃ ⟨hvc, hmemC⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₃
    have hcall := (S.meets (d := d+1) (a := a+r.a*g) (b := b+r.b*g) (c := c+r.c*g)
      (nA := _root_.ThreeSum.BandWeightedScore.length nA g r.a) (nB := _root_.ThreeSum.BandWeightedScore.length nB g r.b) (nC := _root_.ThreeSum.BandWeightedScore.length nC g r.c)
      primes hw hq hqmax (by omega) (by omega) (by omega) haux
      (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..) (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..) (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..) hspace hscoreWord (by omega)
      (fun i hi => by rw [Nat.add_assoc]; exact hA _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
      (fun i hi => by rw [Nat.add_assoc]; exact hB _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi))
      (fun i hi => by rw [Nat.add_assoc]; exact hC _ (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.position_lt hi)) hread hprime hinj hproduct).mono_time
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.score_time_le maxMod s U (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..) (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..) (_root_.ThreeSum1960614.Machine.ThreeSum.BandWeightedScore.length_le ..))
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hva, hvb, hvc]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hva, hvb, hvc] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hva, hvb, hvc] <;> omega)
       on_goal -1 => (rintro value ν ⟨hvalue, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨?_,hkeep⟩
    change value=_
    rw [hvalue,_root_.ThreeSum.BandWeightedScore.block,if_pos hfNat]
    simp only [Nat.add_assoc]
  · (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
    exact ⟨by rw [_root_.ThreeSum.BandWeightedScore.block,if_neg (show r.flag ≠ 1 by omega)]; rfl,fun _ _ => rfl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.meets__implementation_01223db19d) := (@ThreeSum1960614.Machine.ThreeSum.LightBandWeightedScoreCell.meets__implementation_01223db19d)

#print axioms solution
