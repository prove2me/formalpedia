-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:41:37.980978+00:00
-- url     : https://prove2.me/submissions/2410d482-8a51-48d0-9843-9165bfce77c0

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceBucketSetup_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceResidues_ends
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWantedJoin_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedPairs_mem_pairs
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_WantedPairs_pairs_nodup

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightWantedJoin
end ThreeSum.LightWantedJoin
namespace ThreeSum.LightWantedSetup
end ThreeSum.LightWantedSetup
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.SourceBucketView
end ThreeSum.SourceBucketView
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs
namespace ThreeSum.WantedResidueKeys
end ThreeSum.WantedResidueKeys
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
end ThreeSum1960614.Machine.ThreeSum.LightWantedJoin
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedSetup
end ThreeSum1960614.Machine.ThreeSum.LightWantedSetup
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.SourceBucketView
end ThreeSum1960614.Machine.ThreeSum.SourceBucketView
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

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

















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact relocation of closed verified procedure libraries

Every procedure call is shifted by the same list offset. The structural
execution proof preserves the exact initial/final states, runtime, memory
addresses, values, and depth budget. It permits composition of independently
verified fixed programs without assuming a new implementation contract.
-/

namespace ThreeSum.ReportingHostRelocation
open _root_.ThreeSum.ReportingHostRelocation


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light





theorem lookup {P : _root_.ThreeSum1960614.Machine.Light.Program} {p : ℕ} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} (h : P[p]? = some body) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P)[prefixProgram.length+p]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body) := by
  apply _root_.ThreeSum1960614.Machine.Light.getElem?_append_length_add
  rw [List.getElem?_map,h]
  rfl

theorem exec {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ σ' : _root_.ThreeSum1960614.Machine.Light.State} {c : ℕ}
    (h : _root_.ThreeSum1960614.Machine.Light.Exec lim P d s σ σ' c) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Exec lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ σ' c := by
  induction h with
  | skip => exact _root_.ThreeSum1960614.Machine.Light.Exec.skip
  | set h => exact _root_.ThreeSum1960614.Machine.Light.Exec.set h
  | store h₁ h₂ h₃ => exact _root_.ThreeSum1960614.Machine.Light.Exec.store h₁ h₂ h₃
  | seq _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.seq ih₁ ih₂
  | iteTrue h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue h₁ h₂ ih
  | iteFalse h₁ h₂ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse h₁ h₂ ih
  | whileFalse h₁ h₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileFalse h₁ h₂
  | whileTrue h₁ h₂ _ _ ih₁ ih₂ => exact _root_.ThreeSum1960614.Machine.Light.Exec.whileTrue h₁ h₂ ih₁ ih₂
  | call h₁ h₂ h₃ _ ih => exact _root_.ThreeSum1960614.Machine.Light.Exec.call h₁ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup h₂ prefixProgram) h₃ ih

theorem ends {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) d (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length s) σ T Q := by
  obtain ⟨σ',c,he,hc,hq⟩ := h
  exact ⟨σ',c,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.exec he prefixProgram,hc,hq⟩

theorem meets {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {p d : ℕ} {vals : List ℤ} {μ : ℕ → ℤ}
    {T : ℕ} {R : ℤ → (ℕ → ℤ) → Prop} (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (prefixProgram : _root_.ThreeSum1960614.Machine.Light.Program) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.program prefixProgram P) (prefixProgram.length+p) d vals μ T R := by
  obtain ⟨body,hbody,he⟩ := h
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate prefixProgram.length body,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.lookup hbody prefixProgram,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.ends he prefixProgram⟩

end ThreeSum.ReportingHostRelocation

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

































theorem bucketList_length (μ : ℕ → ℤ) (flat start length : ℕ) :
    (_root_.ThreeSum.SourceBuckets.bucketList μ flat start length).length = length := by simp [_root_.ThreeSum.SourceBuckets.bucketList]









end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input residue keys with a carry offset

The source histogram uses `(x % p + shift) % m`, with two independently
chosen moduli. This procedure computes both remainders from each original
signed input and retains every incidence, including duplicate values.
-/

namespace ThreeSum.LightSourceResidues
open _root_.ThreeSum.LightSourceResidues


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000



theorem key_cast {p m : ℕ} (hm : 0 < m) (shift x : ℤ) :
    (_root_.ThreeSum.LightSourceResidues.key p m shift x : ℤ) = (x % (p : ℤ) + shift) % (m : ℤ) := by
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hm.ne'))

theorem key_lt {p m : ℕ} (hm : 0 < m) (shift x : ℤ) : _root_.ThreeSum.LightSourceResidues.key p m shift x < m := by
  have h := Int.emod_lt_of_pos (x % (p : ℤ) + shift)
    (by exact_mod_cast hm : (0 : ℤ) < m)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_cast hm] at h
  exact_mod_cast h











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem meets {pMain pEmod : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.body pEmod)) (hem : P[pEmod]? = some _root_.ThreeSum1960614.Machine.Light.emodBody)
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space) (hsep : _root_.Light.Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,dst,n,p,m,work,shift] μ (_root_.ThreeSum.LightSourceResidues.time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
      _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst n) := by
  exact _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.ends hem hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues)



theorem program_meets
    {μ : ℕ → ℤ} {src dst n p m work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ work) (hdst : dst+n ≤ work)
    (hspace : _root_.ThreeSum.LightSourceResidues.space work p U D ≤ lim.space) (hsep : _root_.Light.Apart src n dst n)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (_root_.ThreeSum.LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.program 0 d [src,dst,n,p,m,work,shift] μ (_root_.ThreeSum.LightSourceResidues.time n p U D) (fun _ ν =>
      (∀ i < n, ν (dst+i) = (_root_.ThreeSum.LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
      _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν work dst n) := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.meets rfl rfl hw hd hp hm hsrc hdst hspace hsep hshift hword hvalues



end ThreeSum.LightSourceResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView
open _root_.ThreeSum.SourceBucketView


open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram






theorem start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBucketView.start μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N r := by
  simp only [_root_.ThreeSum.SourceBucketView.start,H.offsets r hr,Int.toNat_natCast]

theorem stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.stop μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N (r+1) := by
  unfold _root_.ThreeSum.SourceBucketView.stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]

theorem length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.length μ offsets r = _root_.ThreeSum.LightHistogram.count key r N := by
  rw [_root_.ThreeSum.SourceBucketView.length,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.stop_eq H hr,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  omega

theorem indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.indices μ offsets flat r = _root_.ThreeSum.SourceBuckets.bucketList μ flat (_root_.ThreeSum.SourceBuckets.offset key N r) (_root_.ThreeSum.LightHistogram.count key r N) := by
  rw [_root_.ThreeSum.SourceBucketView.indices,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.length_eq H hr]

theorem indices_length {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    (_root_.ThreeSum.SourceBucketView.indices μ offsets flat r).length = _root_.ThreeSum.LightHistogram.count key r N := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.indices_eq H hr,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.bucketList_length]









end ThreeSum.SourceBucketView

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs
open _root_.ThreeSum.WantedPairs


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open scoped _root_.BigOperators

set_option maxHeartbeats 1200000



@[simp] theorem count_zero (left right : ℕ → ℕ) (NR : ℕ) : _root_.ThreeSum.WantedPairs.count left right NR 0=0 := by
  simp [_root_.ThreeSum.WantedPairs.count]

theorem count_succ (left right : ℕ → ℕ) (NR n : ℕ) :
    _root_.ThreeSum.WantedPairs.count left right NR (n+1)=_root_.ThreeSum.WantedPairs.count left right NR n+_root_.ThreeSum.LightHistogram.count right (left n) NR :=
  Finset.sum_range_succ _ _









theorem pairs_succ (μ : ℕ → ℤ) (offsets flat : ℕ) (left : ℕ → ℕ) (n : ℕ) :
    _root_.ThreeSum.WantedPairs.pairs μ offsets flat left (n+1)=_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n++_root_.ThreeSum.WantedPairs.row μ offsets flat left n := by
  simp only [_root_.ThreeSum.WantedPairs.pairs,List.range_succ,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

theorem row_length {μ : ℕ → ℤ} {offsets flat NR M i : ℕ} {left right : ℕ → ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) (hi : left i < M) :
    (_root_.ThreeSum.WantedPairs.row μ offsets flat left i).length=_root_.ThreeSum.LightHistogram.count right (left i) NR := by
  rw [_root_.ThreeSum.WantedPairs.row,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.indices_length H hi]

theorem pairs_length {μ : ℕ → ℤ} {offsets flat NR M : ℕ} {left right : ℕ → ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) : ∀ n,
    (∀ i < n, left i < M) →
      (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n).length=_root_.ThreeSum.WantedPairs.count left right NR n := by
  intro n
  induction n with
  | zero => intro _; simp [_root_.ThreeSum.WantedPairs.pairs]
  | succ n ih =>
    intro hleft
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_succ,List.length_append,ih (fun i hi => hleft i (by omega)),
      _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.row_length H (hleft n (by omega)),_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.count_succ]













theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    _root_.ThreeSum.LightResidues.residue M 1 b=_root_.ThreeSum.LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







end ThreeSum.WantedPairs

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A literal output-sensitive join of original-position residue arrays

The host reads each left code and visits only its matching retained right
fiber. Recursion gives a sum of actual row costs; it never charges or scans
the full left/right Cartesian product. The output contains every matching
original-position pair exactly once.
-/

namespace ThreeSum.LightWantedJoin
open _root_.ThreeSum.LightWantedJoin


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.WantedPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem program_meets {keys offsets flat NR M dst n d : ℕ} {μ : ℕ → ℤ}
    (left right : ℕ → ℕ) (hright : ∀ j < NR, right j < M)
    (hw : (lim.space : ℤ) ≤ lim.word) (hkeys : keys+n ≤ dst)
    (hoffsets : offsets+M+1 ≤ dst) (hflat : flat+NR ≤ dst)
    (hspace : dst+2*_root_.ThreeSum.WantedPairs.count left right NR n ≤ lim.space) (hd : d+n+2 ≤ lim.depth)
    (hleft : ∀ i < n, left i < M) (hread : ∀ i < n, μ (keys+i)=(left i : ℤ))
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.program 0 d [keys,offsets,flat,n,NR,M,dst] μ (_root_.ThreeSum.LightWantedJoin.time left right NR n)
      (fun r ν => r=(_root_.ThreeSum.WantedPairs.count left right NR n : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.WantedPairs.cells (_root_.ThreeSum.WantedPairs.pairs μ offsets flat left n)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.meets rfl rfl left right hright n d μ hw hkeys hoffsets hflat hspace hd hleft hread H

end ThreeSum.LightWantedJoin

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual residue scans and the selected wanted mass

The two-remainder source scanner specializes to an ordinary shifted residue
when its moduli agree. Its actual fiber count is exactly the incidence mass
minimized by the original signed-array offset program.
-/

namespace ThreeSum.WantedResidueKeys
open _root_.ThreeSum.WantedResidueKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open scoped _root_.BigOperators



theorem code_eq_residue (M : ℕ) (shift x : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.code M shift x=_root_.ThreeSum.LightResidues.residue M 1 (x+shift) := by
  simp only [_root_.ThreeSum.WantedResidueKeys.code,_root_.ThreeSum.LightSourceResidues.key,_root_.ThreeSum.LightResidues.residue,one_mul]
  congr 1
  rw [Int.add_emod,Int.emod_emod,← Int.add_emod]

theorem code_lt {M : ℕ} (hM : 0 < M) (shift x : ℤ) : _root_.ThreeSum.WantedResidueKeys.code M shift x < M :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.key_lt hM shift x

theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.code M 0 b=_root_.ThreeSum.WantedResidueKeys.code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,add_zero]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.residue_eq_iff hM a b shift











end ThreeSum.WantedResidueKeys

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWantedSetup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program_meets__implementation_4edb1db6e7 {μ : ℕ → ℤ} {a b NL NR M free U D d : ℕ} {shift : ℤ}
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word) (hM : 0 < M)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : _root_.ThreeSum.LightWantedSetup.space free M left right NL NR U D shift ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceResidues.word M M U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ)) (hd : d+NL+5 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program 11 d [a,b,NL,NR,M,shift,free] μ (_root_.ThreeSum.LightWantedSetup.time M left right NL NR U D shift)
      (fun r ν => r=(free : ℤ) ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output ν free M left right NL NR shift ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let lc := _root_.ThreeSum.LightWantedSetup.leftCodes free
  let rc := _root_.ThreeSum.LightWantedSetup.rightCodes free NL
  let bb := _root_.ThreeSum.LightWantedSetup.bucketBase free NL NR
  let off := _root_.ThreeSum.LightSourceBucketSetup.offsets bb M
  let flat := _root_.ThreeSum.LightSourceBucketSetup.flat bb M
  let dst := _root_.ThreeSum.LightWantedSetup.pairBase free NL NR M
  let lkey := fun i => _root_.ThreeSum.WantedResidueKeys.code M shift (left i)
  let rkey := fun j => _root_.ThreeSum.WantedResidueKeys.code M 0 (right j)
  have hjoinTime : _root_.ThreeSum.LightWantedJoin.time lkey rkey NR NL=
      _root_.ThreeSum.LightWantedJoin.time (fun i => _root_.ThreeSum.WantedResidueKeys.code M shift (left i)) (fun j => _root_.ThreeSum.WantedResidueKeys.code M 0 (right j)) NR NL := rfl
  have hscanSpace : _root_.ThreeSum.LightSourceResidues.space dst M U D ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hpairSpace : dst+2*_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hdst : dst=free+4+NL+NR+3*M+1+NR := rfl
  have hlc : lc=free+4 := rfl
  have hrc : rc=free+4+NL := rfl
  have hbb : bb=free+4+NL+NR := rfl
  have hoff : off=bb+M := rfl
  have hflat : flat=bb+3*M+1 := rfl
  have h3M : (3*(M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3*M ≤ lim.space by omega) : (3*(M : ℤ)) ≤ lim.space).trans hw
  have hDWord : (D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightSourceResidues.word; omega)).trans hword
  have hlkey : ∀ i < NL, lkey i < M := fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_lt hM _ _
  have hrkey : ∀ j < NR, rkey j < M := fun _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_lt hM _ _
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 11) (by rfl : program[11]? = some (body 0 2 9))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.body _root_.ThreeSum.LightWantedSetup.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (lc : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lc, _root_.ThreeSum.LightWantedSetup.leftCodes]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [lc, _root_.ThreeSum.LightWantedSetup.leftCodes] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lc, _root_.ThreeSum.LightWantedSetup.leftCodes] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (rc : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, rc, _root_.ThreeSum.LightWantedSetup.rightCodes, lc]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [rc, _root_.ThreeSum.LightWantedSetup.rightCodes, lc] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, rc, _root_.ThreeSum.LightWantedSetup.rightCodes, lc] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (bb : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, bb, _root_.ThreeSum.LightWantedSetup.bucketBase, rc]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [bb, _root_.ThreeSum.LightWantedSetup.bucketBase, rc] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, bb, _root_.ThreeSum.LightWantedSetup.bucketBase, rc] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (off : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, off, _root_.ThreeSum.LightSourceBucketSetup.offsets]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [off, _root_.ThreeSum.LightSourceBucketSetup.offsets] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, off, _root_.ThreeSum.LightSourceBucketSetup.offsets] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (flat : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, flat, _root_.ThreeSum.LightSourceBucketSetup.flat]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [flat, _root_.ThreeSum.LightSourceBucketSetup.flat] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, flat, _root_.ThreeSum.LightSourceBucketSetup.flat] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dst, _root_.ThreeSum.LightWantedSetup.pairBase, _root_.ThreeSum.LightSourceBucketSetup.next, flat]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [dst, _root_.ThreeSum.LightWantedSetup.pairBase, _root_.ThreeSum.LightSourceBucketSetup.next, flat] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dst, _root_.ThreeSum.LightWantedSetup.pairBase, _root_.ThreeSum.LightSourceBucketSetup.next, flat] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hsL := (((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.program_meets (d := d+1) (μ := μ)
    (src := a) (dst := lc) (n := NL) (p := M) (m := M) (work := dst)
    (U := U) (D := D) (shift := shift) hw (by omega) hM hM (by omega) (by omega)
    hscanSpace (Or.inl (by omega)) hshift hword
    (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 2))).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 9))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.body 0 2 9]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsL _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsL ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.WantedResidueKeys.code]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.WantedResidueKeys.code] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.WantedResidueKeys.code] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨hcodesL, hkeepL⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreadL (i : ℕ) (hi : i < NL) : μ₁ (lc+i)=(lkey i : ℤ) := by
    rw [hcodesL i hi,hleft i hi]
    rfl
  have hsR := (((_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.program_meets (d := d+1) (μ := μ₁)
    (src := b) (dst := rc) (n := NR) (p := M) (m := M) (work := dst)
    (U := U) (D := D) (shift := 0) hw (by omega) hM hM (by omega) (by omega)
    hscanSpace (Or.inl (by omega)) (by simp) hword
    (fun j hj => by rw [hkeepL _ ⟨by omega,Or.inl (by omega)⟩,hright j hj]; exact hvaluesR j hj)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 2))).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 9))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.body 0 2 9]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsR _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsR ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.WantedResidueKeys.code]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.WantedResidueKeys.code] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.WantedResidueKeys.code] <;> omega)
     on_goal -1 => (rintro _ μ₂ ⟨hcodesR, hkeepR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreadR (j : ℕ) (hj : j < NR) : μ₂ (rc+j)=(rkey j : ℤ) := by
    rw [hcodesR j hj,hkeepL _ ⟨by omega,Or.inl (by omega)⟩,hright j hj]
    rfl
  have hleft₂ (i : ℕ) (hi : i < NL) : μ₂ (lc+i)=(lkey i : ℤ) :=
    (hkeepR _ ⟨by omega,Or.inl (by omega)⟩).trans (hreadL i hi)
  have hbuckets := ((_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightSourceBucketSetup.programProcs.meets (d := d+1) (μ := μ₂)
      (keys := rc) (N := NR) (M := M) (base := bb) rkey hw (by omega) hM
      (by omega) (by change dst ≤ lim.space; omega) hrkey hreadR)
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues.program).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 9))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.body 0 2 9]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hbuckets _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hbuckets ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceBucketSetup.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceBucketSetup.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceBucketSetup.time] <;> omega)
     on_goal -1 => (rintro next μ₃ ⟨hnext, H, hcounts, hkeepB⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hleft₃ (i : ℕ) (hi : i < NL) : μ₃ (lc+i)=(lkey i : ℤ) :=
    (hkeepB _ (by omega)).trans (hleft₂ i hi)
  have hj := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedJoin.program_meets (d := d+1) (μ := μ₃) (keys := lc)
      (offsets := off) (flat := flat) (NR := NR) (M := M) (dst := dst) (n := NL)
      lkey rkey hrkey hw (by omega) (by omega) (by omega) hpairSpace (by omega)
      hlkey hleft₃ H) _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.bucketProgram).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.body 0 2 9]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hj _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hj ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, lkey, rkey, _root_.ThreeSum.WantedResidueKeys.code]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [lkey, rkey, _root_.ThreeSum.WantedResidueKeys.code] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, lkey, rkey, _root_.ThreeSum.WantedResidueKeys.code] <;> omega)
     on_goal -1 => (rintro matchCount μ₄ ⟨hmatch, hpairs, hkeepJ⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hmatchTotal : matchCount=(_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift : ℤ) := hmatch
  have htwoWord : (2*(_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 2*_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift ≤ lim.space by omega) :
      (2*(total M left right NL NR shift : ℤ)) ≤ lim.space).trans hw
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen free (_root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmatchTotal]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmatchTotal] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmatchTotal] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 1) (dst : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 2) (dst + 2 * _root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmatchTotal]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmatchTotal] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmatchTotal] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 3) shift ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (free : ℕ) ?_ ?_ ?_
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
  refine ⟨rfl,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,_root_.ThreeSum.WantedPairs.pairs μ₃ off flat lkey NL,?_,?_,?_,?_⟩
    · simp
    · simp [dst]
    · simp [dst]
    · simp
    · exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_length H NL hlkey
    · exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.pairs_nodup H hlkey hrkey
    · intro i j
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.mem_pairs H hlkey hrkey]
      simp only [lkey,rkey,_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_iff hM]
    · intro i hi
      change Function.update (Function.update (Function.update (Function.update μ₄ free _)
        (free+1) _) (free+2) _) (free+3) _ (dst+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
        Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hpairs i hi
  · intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₄ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    rw [hkeepJ _ (by omega),hkeepB _ (by omega),
      hkeepR _ ⟨by omega,Or.inl (by omega)⟩,hkeepL _ ⟨by omega,Or.inl (by omega)⟩]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program_meets__implementation_4edb1db6e7) := (@ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program_meets__implementation_4edb1db6e7)

#print axioms solution
