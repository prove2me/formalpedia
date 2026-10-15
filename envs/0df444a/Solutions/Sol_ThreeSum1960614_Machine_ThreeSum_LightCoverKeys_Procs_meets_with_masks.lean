-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.Procs.meets_with_masks
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:47:24.406279+00:00
-- url     : https://prove2.me/submissions/caa8cdcd-b775-420c-9680-60f28a18ada0

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
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
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightGlobalKeys_Procs_meets_with_masks
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverInit_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverTables_Data_of_kept

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightCoverKeys
end ThreeSum.LightCoverKeys
namespace ThreeSum.LightLocalCoverRetention
end ThreeSum.LightLocalCoverRetention
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightCoverKeys
end ThreeSum1960614.Machine.ThreeSum.LightCoverKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
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

























/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





















































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention
open _root_.ThreeSum.LightLocalCoverRetention


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h ∧
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr
    _root_.ThreeSum.LightCoverGreedy.total _root_.ThreeSum.LightCoverGreedy.out
  omega

theorem data_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h))
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data ν h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h) := by
  obtain ⟨hm,hl,hr,hx,_⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.table_ends_le base h
  exact H.of_kept K hm hl hr hx

theorem rows_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows μ h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h))
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows ν h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h) := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (2*(464*h)) (show s+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h by omega)
  simp only [Nat.add_mul,one_mul] at hm
  rw [K _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree; omega),K _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree; omega)]
  exact H s hs i hi

theorem indices_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ))
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h)) :
    ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ) := by
  intro s
  have he := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.table_ends_le base h).2.2.2.2
  rw [K _ (by have hs := s.isLt; omega)]
  exact H s

theorem header_of_kept {μ ν : ℕ → ℤ} {free h : ℕ}
    (H : _root_.ThreeSum1960614.Machine.Light.Seg μ free (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values free h))
    (K : _root_.ThreeSum1960614.Machine.Light.Kept μ ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h)) :
    _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values free h) := by
  have he : free+20 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h
  apply H.congr
  intro i hi
  have hi' : i < 20 := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hi
  exact K _ (by omega)



end ThreeSum.LightLocalCoverRetention

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.Procs.meets_with_masks__implementation_8620cd7013 {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+J+11 ≤ lim.depth)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.space free h J ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.word h J : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [h,J,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time h J)
      (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J : ℤ) ∧
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J)=((_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.keyHeader free h J+1) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values free h) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data ν h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps (_root_.ThreeSum.LightLocalCoverInit.base free) h)
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 (_root_.ThreeSum.LightLocalCoverInit.base free) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 (_root_.ThreeSum.LightLocalCoverInit.base free) h)
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr (_root_.ThreeSum.LightLocalCoverInit.base free) h) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows ν h (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base free) h) ∧
        (∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h, ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates (_root_.ThreeSum.LightLocalCoverInit.base free) h+s.val)=
          (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ)) ∧
        (∀ i < _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h, ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h+i)=
          (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hcspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.space free h ≤ lim.space := (le_max_left _ _).trans hspace
  have hkspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h) h J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hcword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.word h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hkword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbaseNext : free+20 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.base_le_nextFree (_root_.ThreeSum.LightLocalCoverInit.base free) h
  have hnextSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h ≤ lim.space := by
    have hs : _root_.ThreeSum.LightLocalKeyRow.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch (_root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h) h)
        (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) ≤ lim.space :=
      (le_max_left _ _).trans hkspace
    unfold _root_.ThreeSum.LightLocalKeyRow.space _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch at hs
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.body _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.cover.meets (d := d + 1) hw (by omega) hcspace hcword) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro next μ₁ ⟨hnext, hheader, hdata, hrows, hindices, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have h0 : μ₁ free=(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 0 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have h6 : μ₁ (free+6)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 6 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have h8 : μ₁ (free+8)=(464*h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 8 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have h9 : μ₁ (free+9)=(2*h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 9 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have h10 : μ₁ (free+10)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 10 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have h12 : μ₁ (free+12)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base free) h : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using hheader 12 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverInit.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values])
  have hk := S.keys.meets_with_masks (d := d+1) (h := h) (J := J)
    (maps := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base free) h) (free := _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover free h)
    hw (by omega) hkspace hkword le_rfl
    (fun j hj i hi => (hrows j hj i hi).1) (fun j hj i hi => (hrows j hj i hi).2)
  have haddress (i : ℕ) : ((free : ℤ)+(i : ℤ)).toNat=free+i := by omega
  have h6Read : μ₁ (((free : ℤ)+6).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ) := by
    rw [show ((free : ℤ)+6).toNat=free+6 by omega]
    exact h6
  have h8Read : μ₁ (((free : ℤ)+8).toNat)=(464*h : ℤ) := by
    rw [show ((free : ℤ)+8).toNat=free+8 by omega]
    exact h8
  have h9Read : μ₁ (((free : ℤ)+9).toNat)=(2*h : ℤ) := by
    rw [show ((free : ℤ)+9).toNat=free+9 by omega]
    exact h9
  have h10Read : μ₁ (((free : ℤ)+10).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact h10
  have h12Read : μ₁ (((free : ℤ)+12).toNat)=(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps (_root_.ThreeSum.LightLocalCoverInit.base free) h : ℤ) := by
    rw [show ((free : ℤ)+12).toNat=free+12 by omega]
    exact h12
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hk _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hk ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, h0, h6Read, h8Read, h9Read, h10Read, h12Read, hnext, _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [h0, h6Read, h8Read, h9Read, h10Read, h12Read, hnext, _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, h0, h6Read, h8Read, h9Read, h10Read, h12Read, hnext, _root_.ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.afterCover] <;> omega)
     on_goal -1 => (rintro result μ₂ ⟨hr, hcount, hkeys, hmasks, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hr,hcount,hkeys,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.header_of_kept hheader hkeep₂,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.data_of_kept hdata hkeep₂,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.rows_of_kept hrows hkeep₂,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverRetention.indices_of_kept hindices hkeep₂,hmasks,?_⟩
  intro a ha
  exact (hkeep₂ a (by omega)).trans (hkeep₁ a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.Procs.meets_with_masks__implementation_8620cd7013) := (@ThreeSum1960614.Machine.ThreeSum.LightCoverKeys.Procs.meets_with_masks__implementation_8620cd7013)

#print axioms solution
