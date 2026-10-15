-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:36:20.323385+00:00
-- url     : https://prove2.me/submissions/4e889fca-8254-4413-8b79-fa2e9bee5c85

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingCatalogBatch_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingFilter_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_ReportingHostSuffixValueBounds_prefix_count_le_word

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingCatalogLevel
end ThreeSum.LightReportingCatalogLevel
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
end ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/

/-- A procedure of a program is a procedure, with the same number, of the program with more
procedures appended. -/
theorem getElem?_append_of_eq_some {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body)
    (R : _root_.ThreeSum1960614.Machine.Light.Program) : (P ++ R)[p]? = some body := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h).1]
  exact h





/-- A run stays a run when procedures are appended to the program. -/
theorem Exec.append {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (P ++ R) d s σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some h₂ R) h₃ ih

/-! ## The rules -/





/-- What is proved about a program holds for the program with more procedures appended. -/
theorem Ends.append {s σ T Q} (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (R : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (P ++ R) d s σ T Q := by
  obtain ⟨σ', c, he, hc, hq⟩ := h
  exact ⟨σ', c, he.append R, hc, hq⟩























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







/-! ## The limits -/









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







/-- A specification holds for the program with more procedures appended. -/
theorem Meets.append (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (P' : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (P ++ P') p d vals μ T R := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, _root_.ThreeSum1960614.Machine.Light.getElem?_append_of_eq_some hp P', he.append P'⟩

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





















/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)





/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]









/-- A segment of natural numbers that does not meet the region is kept. -/
theorem SegN.of_sameOutside {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.SegN μ' b l :=
  _root_.ThreeSum1960614.Machine.Light.Seg.of_sameOutside h hs (by simpa using hd)















end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program_meets__implementation_f565043310
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase indexBase ptrBase inL inR n dst selected maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pres : ℕ → List (Finset (Fin (464*h)))) (hk : k ≤ J)
    (hp : ∀ i < n, _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k (pres i))
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ dst)
    (hdataR : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ dst)
    (hindex : indexBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ dst) (hptr : ptrBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ dst)
    (hboxesEnd : boxBase+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut ≤ dst)
    (hinL : inL+n ≤ dst) (hinR : inR+n ≤ dst)
    (hdst : dst+n ≤ selected) (hselected : selected+n ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) ≤ lim.space)
    (hpowSpace : work+(2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+2) ≤ lim.space)
    (hemodSpace : work+(Nat.log 2 (_root_.ThreeSum.LightReportingCatalogLookup.valueBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+1)+2) ≤ lim.space)
    (hword : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hlookupWord : (_root_.ThreeSum.LightReportingCatalogLookup.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) (hboxCut : boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k)
    (hflags : _root_.ThreeSum.LightBlockQuery.residualSize h J k-t ≤ boxCut)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hindexData : ∃ S : List ℤ, _root_.ThreeSum1960614.Machine.Light.Seg μ indexBase S ∧
      S.Perm (_root_.ThreeSum.ReportingHostPackedCatalog.codes (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPackedCatalog.prefixKey h J k) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)) ∧
      S.Pairwise (· ≤ ·))
    (hptrs : _root_.ThreeSum1960614.Machine.Light.SegN μ ptrBase (List.ofFn fun i : Fin (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) =>
      boxBase+i.val*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut))
    (hboxes : ∀ i < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k, _root_.ThreeSum.LightBoxStages.StoredThrough μ
      (boxBase+i*_root_.ThreeSum.LightReportingSuffixCatalog.stride (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut) boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
        (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preL h J k i) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder.preR h J k i))
      (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k))
    (hreadL : ∀ i < n, μ (inL+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (pres i))) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) =
      (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) (pres i))) : ℤ))
    (hd : depth+2*_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+14 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program 38 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,_root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*h,k*h,
        _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*(464*h),_root_.ThreeSum.LightBlockQuery.residualSize h J k,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),
        t,baseL,baseR,boxCut,indexBase,ptrBase,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,inL,inR,n,dst,maskBase,work,selected]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time h J k t n)
      (fun r μ' =>
        let counts := fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
        r = ((_root_.ThreeSum.LightReportingFilter.selected counts n).length : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' selected (_root_.ThreeSum.LightReportingFilter.selected counts n) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dst (List.ofFn fun i : Fin n => counts i.val) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' dst) := by
  let counts := fun i => _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k (pres i)
  have hcountWord (i : ℕ) (hi : i < n) : (counts i : ℤ) ≤ lim.word :=
    _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffixValueBounds.prefix_count_le_word pMod shift A B C a b c w (pres i)
      hk (hp i hi) hkey hvalueWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 38) (by rfl : program[38]? = some (body 36 37))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.body _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.time
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.program_meets (depth := depth+1) (μ := μ)
    (inL := inL) (inR := inR) (n := n) (dst := dst) (maskBase := maskBase) (work := work)
    pMod shift A B C a b c w pres hk hp hkey hw hdataL hdataR hindex hptr hboxesEnd
    hinL hinR (by omega) hmasks hspace hpowSpace hemodSpace hword hlookupWord hvalueWord
    ht hboxCut hflags hstoredL hstoredR hindexData hptrs hboxes hreadL hreadR (by omega)).append _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.suffix
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time] <;> omega)
     on_goal -1 => (rintro ret μ₁ ⟨hcounts, hkeepBatch⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreads (i : ℕ) (hi : i < n) : μ₁ (dst+i) = (counts i : ℤ) := by
    have hs := hcounts.getElem (i := i) (by simpa only [List.length_ofFn] using hi)
    simpa only [List.getElem_ofFn] using hs
  have hf := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingFilter.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program) (p := 37) (d := depth+1)
    (μ := μ₁) (src := dst) (dst := selected) (n := n) counts rfl hw (by omega) (by omega)
    (Or.inl hdst) hcountWord hreads
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hf _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hf ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogBatch.time, _root_.ThreeSum.LightReportingFilter.time] <;> omega)
     on_goal -1 => (rintro found μ₂ ⟨hfound, hselectedOut, hkeepFilter⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hfound,hselectedOut,?_,?_⟩
  · exact hcounts.of_sameOutside hkeepFilter (Or.inl (by simpa using hdst))
  · intro i hi
    exact (hkeepFilter i (Or.inl (by omega))).trans (hkeepBatch i ⟨by omega,Or.inl hi⟩)
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program_meets__implementation_f565043310.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingCatalogLevel.program_meets__implementation_f565043310.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
