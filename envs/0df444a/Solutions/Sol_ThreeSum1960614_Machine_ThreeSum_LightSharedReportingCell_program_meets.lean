-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:44:54.883988+00:00
-- url     : https://prove2.me/submissions/13a58acd-deee-4491-9107-c437b5c6080e

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetSize_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSharedReportingEntry_program_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightDownsetSize
end ThreeSum.LightDownsetSize
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LightSharedReportingCell
end ThreeSum.LightSharedReportingCell
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
end ThreeSum1960614.Machine.ThreeSum.LightDownsetSize
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega





theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) :
    _root_.ThreeSum.SubsetAddress.downsetRank L m < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hmask : _root_.ThreeSum.SubsetAddress.IsMask L (_root_.ThreeSum.SubsetAddress.weight L m) m := ⟨hm, rfl⟩
  have hr := _root_.ThreeSum.SubsetAddress.layerRank_lt hmask
  unfold _root_.ThreeSum.SubsetAddress.downsetRank _root_.ThreeSum.SubsetAddress.downsetCap
  calc
    _ < _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m) + L.choose (_root_.ThreeSum.SubsetAddress.weight L m) := Nat.add_lt_add_left hr _
    _ = _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m + 1) := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L _).symm
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))





















































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    _root_.ThreeSum.SubsetAddress.subsetRank s < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask s
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.downsetRank_lt hm.1 (hm.2.trans_le hs)











end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

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
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize
open _root_.ThreeSum.LightDownsetSize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}











theorem program_procs : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program 0 d [L,cut,work] μ (_root_.ThreeSum.LightDownsetSize.time L)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program_procs rfl hw hspace hword hcut hd



end ThreeSum.LightDownsetSize

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

/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch
open _root_.ThreeSum.LightSignedLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)















end ThreeSum.LightSignedLeafBatch

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual complete shared prefix catalog from the original source tables

A single closed program constructs every aligned prefix-mask pair, reads its
computed count header, and builds all local suffix box tables. The original
record order is exact; no supplied enumeration, count, or table pointer is
used as an algorithmic oracle.
-/

namespace ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingPrefixCatalog


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}











theorem count_pos (h k : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := by
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))







end ThreeSum.LightReportingPrefixCatalog

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact compact layout for a shared reporting catalog cell

The local pair and prefix counts are retained exactly. Each cell reserves
the two prefix arrays, its pointer row, all suffix boxes, the sorted index,
and the polynomial scratch used by the existing constructor. Layout sums
are later computed by the bank setup loop.
-/

namespace ThreeSum.SharedReportingBankLayout
open _root_.ThreeSum.SharedReportingBankLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog

set_option maxHeartbeats 1400000
set_option maxRecDepth 9000























theorem stageR_eq (base h k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k=_root_.ThreeSum.LightRadixKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h) k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan _root_.ThreeSum.LightRadixKeys.space _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega

theorem pointers_eq (base h k : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k=_root_.ThreeSum.LightRadixKeys.space (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h) k := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan _root_.ThreeSum.LightRadixKeys.space _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega

theorem ordered (base h J k boxCut : ℕ) :
    base ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ∧ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes base h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ∧
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL]
  omega





theorem index_end (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work
  omega

theorem cap_end (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k boxCut ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work
  omega

theorem pair_scratch (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+2*(464*h)+2 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega

theorem table_scratch (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+1+_root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth
  omega

theorem sort_scratch (base h J k boxCut : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work base h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish
  omega

theorem downset_scratch {h J k : ℕ} (hk : k ≤ J) (base boxCut : ℕ) :
    base+_root_.ThreeSum.LightPascal.tableSize ((J-k)*(464*h))+((J-k)*(464*h)+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish base h J k boxCut := by
  have hV : (J-k)*(464*h) ≤ J*(464*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have htable : _root_.ThreeSum.LightPascal.tableSize ((J-k)*(464*h)) ≤ _root_.ThreeSum.LightPascal.tableSize (J*(464*h)) := by
    exact Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered base h J k boxCut
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.table_scratch base h J k boxCut
  omega











end ThreeSum.SharedReportingBankLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPrefixOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog
open _root_.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCatalog
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
set_option maxHeartbeats 2900000
set_option maxRecDepth 15000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program_meets__implementation_b92713299e {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ}
    {h J k boxCut baseL baseR cellL cellR free rec B D d t : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(464*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hconstants : (464 : ℤ) ≤ lim.word)
    (hJWord : (J : ℤ) ≤ lim.word)
    (hboxCut : boxCut ≤ (J-k)*(464*h))
    (hcellL : cellL < rec) (hcellR : cellR < rec)
    (hdataL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) (2*h*J) ≤ rec)
    (hdataR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) (2*h*J) ≤ rec)
    (hrec : rec+5 ≤ free)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish free h J k boxCut ≤ lim.space)
    (hpowWord : ((2^(464*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (_root_.ThreeSum.LightRadixKeys.word (2^(464*h)) (2^(464*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(464*h)+1)*2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (_root_.ThreeSum.LightReportingSortedCatalog.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (((2^((J-k)*(464*h))*
      ((2^((J-k)*(464*h))*B)*(2^((J-k)*(464*h))*D))) : ℕ) : ℤ) ≤ lim.word)
    (htWord : (t : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ 2*h*J) (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(464*h)))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(464*h)))
    (hdPair : d+464*h+k+8 ≤ lim.depth) (hd : d+J*(464*h)+17 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k)+5 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program 62 d
      [h,J,k,cellL,cellR,t,boxCut,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k,rec,free]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.time h J k boxCut) (fun r ν =>
        r=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish free h J k boxCut : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankData.Entry ν rec (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.catalog free h J k boxCut t) hk f g ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseL (2*h*J) f (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseR (2*h*J) g (J*(464*h)) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν free rec 5) := by
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.ordered free h J k boxCut
  have hV : (J-k)*(464*h) ≤ J*(464*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hcut : 2*h*J ≤ J*(464*h) := by nlinarith
  have hpairSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pair_scratch free h J k boxCut).trans hspace
  have htableSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.table_scratch free h J k boxCut).trans hspace
  have hsortSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.sort_scratch free h J k boxCut).trans hspace
  have hW : J*(464*h)+1 ≤ lim.space := by omega
  have hL : 464*h ≤ lim.space := by omega
  have hN : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k ≤ lim.space := by omega
  have hsizeSpace := (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.downset_scratch hk free boxCut).trans hspace
  have hsizeWord : ((((J-k)*(464*h)+1)*2^((J-k)*(464*h)+1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (Nat.mul_le_mul (Nat.add_le_add_right hV 1)
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hV 1)))).trans hword
  have hprod : _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut ≤ lim.space := by
    have hm := ho.2.2.2.2.2.2.2.1
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth at hm
    omega
  have hstride : _root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut ≤ lim.space := by
    have hn := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count_pos h k
    exact (Nat.le_mul_of_pos_left _ hn).trans hprod
  have hcap : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k boxCut ≤ lim.space := by
    have hm := ho.2.2.2.2.2.2.2.1
    have hh := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap_end free h J k boxCut
    omega
  have hwork : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work free h J k boxCut ≤ lim.space := by omega
  have hsIndex := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index_end free h J k boxCut
  have hstageL := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR_eq free h k
  have hstageR := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers_eq free h k
  have epairL : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL free h=free+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h := rfl
  have epairR : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR free h=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL free h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h := rfl
  have estageL : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL free h=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR free h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h := rfl
  have estageR : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR free h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL free h+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k := rfl
  have epointers : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers free h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR free h k+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.prefixSpan h k := rfl
  have eboxes : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes free h k=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers free h k+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := rfl
  have emasks : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks free h J k boxCut=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes free h k+
      _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k*_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut := rfl
  have ework : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work free h J k boxCut=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks free h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k boxCut+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := rfl
  have efinish : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish free h J k boxCut=_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work free h J k boxCut+2*(464*h)+2+1+
      _root_.ThreeSum.LightPascal.tableSize (J*(464*h))+(J*(464*h)+1)+_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPrefixCatalog.count h k := rfl
  have ecap : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap h J k boxCut=_root_.ThreeSum.SubsetAddress.downsetCap ((J-k)*(464*h)) boxCut := rfl
  have hWWord : (J : ℤ)*(464*(h : ℤ)) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show J*(464*h) ≤ lim.space by omega)).trans hw
  have hWNonneg : (0 : ℤ) ≤ (J : ℤ)*(464*(h : ℤ)) := by positivity
  have hWScalar : (J : ℤ)*(464*(h : ℤ))=((J*(464*h) : ℕ) : ℤ) := by push_cast; ring
  have etable : ((J : ℤ)*(464*(h : ℤ))+1)*((J : ℤ)*(464*(h : ℤ))+1)=
      (_root_.ThreeSum.LightPascal.tableSize (J*(464*h)) : ℤ) := by simp only [_root_.ThreeSum.LightPascal.tableSize,pow_two,Nat.cast_mul,
        Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hVWord : ((J : ℤ)-(k : ℤ))*(464*(h : ℤ)) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_sub hk,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show (J-k)*(464*h) ≤ lim.space by omega)).trans hw
  have hVNonneg : (0 : ℤ) ≤ ((J : ℤ)-(k : ℤ))*(464*(h : ℤ)) :=
    mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hk)) (by positivity)
  have hVScalar : ((J-k : ℕ) : ℤ)*(464*(h : ℤ))=
      (((J-k)*(464*h) : ℕ) : ℤ) := by push_cast; ring
  have hcutWord : (2 : ℤ)*(h : ℤ)*(J : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show 2*h*J ≤ lim.space by omega)).trans hw
  have hcutNonneg : (0 : ℤ) ≤ (2 : ℤ)*(h : ℤ)*(J : ℤ) := by positivity
  have hprefWord : (k : ℤ)*(464*(h : ℤ)) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hk) (by positivity)).trans hWWord
  have hprefNonneg : (0 : ℤ) ≤ (k : ℤ)*(464*(h : ℤ)) := by positivity
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 62) (by rfl : program[62]?=some (body 53 52))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width h J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth h J k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, Nat.cast_sub hk]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, Nat.cast_sub hk] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, Nat.cast_sub hk] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hsize := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program_meets (μ := μ) (d := d+1) hw hsizeSpace hsizeWord hboxCut (by omega))
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.body 53 52]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsize _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsize ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
     on_goal -1 => (rintro c ν₁ ⟨hc, hkeepSize⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have estride : (((J-k : ℕ) : ℤ)*(464*(h : ℤ))+1)*c=
      (_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J-k)*(464*h)) boxCut : ℤ) := by
    rw [hc]
    simp only [_root_.ThreeSum.LightReportingSuffixCatalog.stride,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hc] at estride
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL free h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR free h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL free h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR free h k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers free h k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes free h k : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightReportingSuffixCatalog.stride ((J - k) * (464 * h)) boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc, _root_.ThreeSum.LightReportingSuffixCatalog.stride, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hc, _root_.ThreeSum.LightReportingSuffixCatalog.stride, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc, _root_.ThreeSum.LightReportingSuffixCatalog.stride, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks free h J k boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work free h J k boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hc, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish free h J k boxCut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.tableSize, pow_two]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.tableSize, pow_two] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.tableSize, pow_two] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 * h * J : ℕ) ?_ ?_ ?_
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
  have hsourceL : _root_.ThreeSum.LightZetaStages.StoredThrough ν₁ baseL (2*h*J) f (J*(464*h)) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro a _ ha; exact hkeepSize a (by omega))
  have hsourceR : _root_.ThreeSum.LightZetaStages.StoredThrough ν₁ baseR (2*h*J) g (J*(464*h)) :=
    _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro a _ ha; exact hkeepSize a (by omega))
  have hreadL : ν₁ cellL=(baseL : ℤ) := (hkeepSize cellL (by omega)).trans hleftRead
  have hreadR : ν₁ cellR=(baseR : ℤ) := (hkeepSize cellR (by omega)).trans hrightRead
  have he := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program_meets (d := d+1) (srcS := free)
    (pairL := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairL free h) (pairR := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pairR free h)
    (stageL := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageL free h) (stageR := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.stageR free h k)
    (ptrBase := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.pointers free h k) (boxBase := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.boxes free h k)
    (maskBase := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.masks free h J k boxCut) (indexBase := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index free h J k boxCut)
    (work := _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.work free h J k boxCut) (t := t) hk f g hw hcut hboxCut hcellL hcellR hdataL hdataR hrec
    (by rfl) (by rfl) (by rfl) hstageL.symm.le hstageR.symm.le
    (by rfl) (by rfl) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.cap_end free h J k boxCut) (by rfl) hsIndex
    hpairSpace htableSpace hsortSpace hpowWord hkeysWord hword hindexWord hvalueWord htWord hpre hf hg
    hreadL hreadR hsourceL hsourceR (by omega) (by omega) (by omega)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingEntry.program.length))).append
        [_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.body 53 52]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen he ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.width, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.suffixWidth, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.index] <;> omega)
     on_goal -1 => (rintro result ν₂ ⟨_, hentry, hsourceL', hsourceR', hkeepEntry⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.finish free h J k boxCut : ℕ) ?_ ?_ ?_
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
  refine ⟨by simp,hentry,hsourceL',hsourceR',?_⟩
  intro a ⟨ha,houtside⟩
  exact (hkeepEntry a ⟨ha,houtside⟩).trans (hkeepSize a ha)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program_meets__implementation_b92713299e) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCell.program_meets__implementation_b92713299e)

#print axioms solution
