-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:50:05.89432+00:00
-- url     : https://prove2.me/submissions/0ea0910b-d0bc-45ec-a461-2191b6ac181f

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
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOriginalOffset_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWantedSetup_program_meets
import Theorems.Thm_ThreeSum_Histograms_correlation_histograms
import Theorems.Thm_ThreeSum_LightMinimum_least_value_le

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Balancing
end ThreeSum.Balancing
namespace ThreeSum.CyclicFold
end ThreeSum.CyclicFold
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.GlobalKeyOffset
end ThreeSum.GlobalKeyOffset
namespace ThreeSum.Histograms
end ThreeSum.Histograms
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBalancedOffset
end ThreeSum.LightBalancedOffset
namespace ThreeSum.LightBalancedWanted
end ThreeSum.LightBalancedWanted
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum
namespace ThreeSum.LightOriginalOffset
end ThreeSum.LightOriginalOffset
namespace ThreeSum.LightResidueHistogram
end ThreeSum.LightResidueHistogram
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.ModuloCounts
end ThreeSum.ModuloCounts
namespace ThreeSum.ReportingHostRelocation
end ThreeSum.ReportingHostRelocation
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
namespace ThreeSum1960614.Machine.ThreeSum.Balancing
end ThreeSum1960614.Machine.ThreeSum.Balancing
namespace ThreeSum1960614.Machine.ThreeSum.CyclicFold
end ThreeSum1960614.Machine.ThreeSum.CyclicFold
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset
namespace ThreeSum1960614.Machine.ThreeSum.Histograms
end ThreeSum1960614.Machine.ThreeSum.Histograms
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
end ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted
end ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightMinimum
end ThreeSum1960614.Machine.ThreeSum.LightMinimum
namespace ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
end ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset
namespace ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
end ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCounts
end ThreeSum1960614.Machine.ThreeSum.ModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
end ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
end ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys

namespace ThreeSum1960614.Machine

/-! # An exact global offset chosen by a cyclic correlation -/

namespace ThreeSum.Balancing
open _root_.ThreeSum.Balancing


open _root_.Finset
open scoped _root_.BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]



theorem sum_correlation (F H : G → ℕ) :
    (∑ d, _root_.ThreeSum.Balancing.correlation F H d) = (∑ k, F k) * (∑ k, H k) := by
  unfold _root_.ThreeSum.Balancing.correlation
  rw [sum_comm]
  simp only [← mul_sum]
  have hshift (k : G) : (∑ d, H (k - d)) = ∑ d, H d := by
    exact Equiv.sum_comp (Equiv.subLeft k) H
  simp_rw [hshift]
  exact (sum_mul ..).symm

/-- The mean is exact for every table, with no hash-uniformity assumption. -/
theorem exists_balanced_offset (F H : G → ℕ) :
    ∃ d, Fintype.card G * _root_.ThreeSum.Balancing.correlation F H d ≤ (∑ k, F k) * (∑ k, H k) := by
  by_contra! h
  have hs : (∑ _d : G, (∑ k, F k) * (∑ k, H k)) <
      ∑ d, Fintype.card G * _root_.ThreeSum.Balancing.correlation F H d := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using h)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum, _root_.ThreeSum1960614.Machine.ThreeSum.Balancing.sum_correlation] at hs
  exact (lt_irrefl _ hs)







end ThreeSum.Balancing

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
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms
open _root_.ThreeSum.Histograms


open _root_.Finset
open scoped _root_.BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]



theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, _root_.ThreeSum.Histograms.histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold _root_.ThreeSum.Histograms.histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp













end ThreeSum.Histograms

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
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum
open _root_.ThreeSum.LightMinimum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : _root_.ThreeSum.LightMinimum.least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [_root_.ThreeSum.LightMinimum.least]
      | succ n =>
          have h := ih (by omega)
          unfold _root_.ThreeSum.LightMinimum.least
          split <;> omega











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightMinimum

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
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset
open _root_.ThreeSum.LightBalancedOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Finset
open scoped _root_.BigOperators



theorem offset_lt {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : _root_.ThreeSum.LightBalancedOffset.offset F H < p :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightMinimum.least_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))

theorem offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * _root_.ThreeSum.Balancing.correlation F H (_root_.ThreeSum.LightBalancedOffset.offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by
  obtain ⟨z, hz⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.Balancing.exists_balanced_offset F H
  have hmin := _root_.ThreeSum.LightMinimum.least_value_le
    (fun r => (_root_.ThreeSum.Balancing.correlation F H (r : ZMod p) : ℤ)) p z.val (ZMod.val_lt z)
  have hminNat : _root_.ThreeSum.Balancing.correlation F H (_root_.ThreeSum.LightBalancedOffset.offset F H : ZMod p) ≤
      _root_.ThreeSum.Balancing.correlation F H z := by
    simpa only [_root_.ThreeSum.LightBalancedOffset.offset, ZMod.natCast_zmod_val, Nat.cast_le] using hmin
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at hz
  exact (Nat.mul_le_mul_left p hminNat).trans hz





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightBalancedOffset

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram
open _root_.ThreeSum.LightResidueHistogram


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, _root_.ThreeSum.LightResidueHistogram.signedHistogram p c values n z) = n := by
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.Histograms.sum_histogram]
  simp



























end ThreeSum.LightResidueHistogram

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts
open _root_.ThreeSum.ModuloCounts


open _root_.Finset
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open scoped _root_.BigOperators















theorem signedHistogram_congr {p c n} {a b : ℕ → ℤ}
    (hab : ∀ i < n, a i = b i) :
    _root_.ThreeSum.LightResidueHistogram.signedHistogram p c a n = _root_.ThreeSum.LightResidueHistogram.signedHistogram p c b n := by
  funext z
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram _root_.ThreeSum.Histograms.histogram
  apply sum_congr rfl
  intro i hi
  simp only [hab i (mem_range.mp hi)]



end ThreeSum.ModuloCounts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset
open _root_.ThreeSum.LightOriginalOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues
open _root_.ThreeSum.LightResidueHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
open _root_.ThreeSum.CyclicFold
open _root_.ThreeSum1960614.Machine.ThreeSum.CyclicFold
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000



theorem selected_lt (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) :
    _root_.ThreeSum.LightOriginalOffset.selected p left right nLeft nRight < p := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.offset_lt ..

/-- The actual selected offset satisfies the exact raw-incidence mean bound,
including duplicate keys in either original array. -/
theorem selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * _root_.ThreeSum.Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (_root_.ThreeSum.LightOriginalOffset.selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedOffset.offset_balanced (_root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 right nRight)
    (_root_.ThreeSum.LightResidueHistogram.signedHistogram p 1 left nLeft)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.sum_signedHistogram,_root_.ThreeSum1960614.Machine.ThreeSum.LightResidueHistogram.sum_signedHistogram] at h
  change p * _root_.ThreeSum.Balancing.correlation _ _ (_root_.ThreeSum.LightOriginalOffset.selected p left right nLeft nRight : ZMod p) ≤ _ at h
  unfold _root_.ThreeSum.LightResidueHistogram.signedHistogram at h
  rw [_root_.ThreeSum.Histograms.correlation_histograms] at h
  simpa only [one_mul,Nat.mul_comm] using h









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









theorem program_meets {a b nLeft nRight p N free U : ℕ} [NeZero p] {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : _root_.ThreeSum.LightOriginalOffset.space free p N U ≤ lim.space) (hword : (_root_.ThreeSum.LightOriginalOffset.word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.program 0 d [a,b,nLeft,nRight,p,N,free] μ (_root_.ThreeSum.LightOriginalOffset.time p nLeft nRight U)
      (fun r ν => r = (_root_.ThreeSum.LightOriginalOffset.selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.programProcs.meets hw ha hb hnLeft hnRight hspace hword hd hLeft hRight



end ThreeSum.LightOriginalOffset

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual array-selected offset balances original output records

The program's right histogram is indexed by literal key-array positions.
This module transports that count bijectively to the original global output
type, retaining distinct outputs that happen to have equal integer keys.
-/

namespace ThreeSum.GlobalKeyOffset
open _root_.ThreeSum.GlobalKeyOffset


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000

















theorem residue_relation_iff (p : ℕ) (left right d : ℤ) :
    (right : ZMod p)-(left : ZMod p)=(d : ZMod p) ↔ (p : ℤ) ∣ left+d-right := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,Int.cast_sub,Int.cast_add,sub_eq_zero]
  constructor
  · intro hh
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh).symm
  · intro hh
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using hh.symm



end ThreeSum.GlobalKeyOffset

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

































theorem residue_eq_iff {M : ℕ} (hM : 0 < M) (a b d : ℤ) :
    _root_.ThreeSum.LightResidues.residue M 1 b=_root_.ThreeSum.LightResidues.residue M 1 (a+d) ↔ (M : ℤ) ∣ a+d-b := by
  rw [← Nat.cast_inj (R := ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hM,one_mul,one_mul]
  exact Int.modEq_iff_dvd







end ThreeSum.WantedPairs

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



theorem code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.code M 0 b=_root_.ThreeSum.WantedResidueKeys.code M shift a ↔ (M : ℤ) ∣ a+shift-b := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_residue,add_zero]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs.residue_eq_iff hM a b shift



theorem total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    _root_.ThreeSum.WantedResidueKeys.total M left right NL NR shift =
      _root_.ThreeSum.Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by
  unfold _root_.ThreeSum.WantedResidueKeys.total _root_.ThreeSum.WantedPairs.count _root_.ThreeSum.LightHistogram.count _root_.ThreeSum.Histograms.pairMass
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter,one_mul,
    _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.code_eq_iff hM,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyOffset.residue_relation_iff]

theorem selected_total_bound (M : ℕ) [NeZero M] (left right : ℕ → ℤ) (NL NR : ℕ) :
    M*_root_.ThreeSum.WantedResidueKeys.total M left right NL NR (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR) ≤ NL*NR := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.total_eq_pairMass M (Nat.pos_of_ne_zero (NeZero.ne M))]
  simpa only [Int.cast_natCast] using _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.selected_pairMass_bound M left right NL NR

theorem selected_congr {M NL NR : ℕ} [NeZero M] {left left' right right' : ℕ → ℤ}
    (hleft : ∀ i < NL, left i=left' i) (hright : ∀ i < NR, right i=right' i) :
    _root_.ThreeSum.LightOriginalOffset.selected M left right NL NR=
      _root_.ThreeSum.LightOriginalOffset.selected M left' right' NL NR := by
  unfold _root_.ThreeSum.LightOriginalOffset.selected
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ModuloCounts.signedHistogram_congr (p := M) (c := 1) hleft,
    _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCounts.signedHistogram_congr (p := M) (c := 1) hright]



end ThreeSum.WantedResidueKeys

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBalancedWanted
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.WantedResidueKeys
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program_meets__implementation_22acf72a44 {μ : ℕ → ℤ} {a b NL NR M free U d : ℕ} [NeZero M]
    (left right : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+NL ≤ free) (hb : b+NR ≤ free)
    (hspace : _root_.ThreeSum.LightBalancedWanted.space free M left right NL NR U ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBalancedWanted.word M NL NR U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 M+NL+6 ≤ lim.depth)
    (hleft : ∀ i < NL, μ (a+i)=left i) (hright : ∀ j < NR, μ (b+j)=right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ (U : ℤ))
    (hvaluesR : ∀ j < NR, |right j| ≤ (U : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program 25 d [a,b,NL,NR,M,free] μ (_root_.ThreeSum.LightBalancedWanted.time M left right NL NR U)
      (fun r ν => r=(free : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.Output ν free M left right NL NR
          (_root_.ThreeSum.LightOriginalOffset.selected M left right NL NR) ∧
        M*(ν free).toNat ≤ NL*NR ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let shift := _root_.ThreeSum.LightOriginalOffset.selected M left right NL NR
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hshift : shift < M := _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.selected_lt ..
  have hshiftAbs : |(shift : ℤ)| ≤ (M : ℤ) := by
    rw [Int.abs_natCast]
    exact Int.ofNat_le.mpr (by omega)
  have hoffSpace : _root_.ThreeSum.LightOriginalOffset.space free M (NL+NR) U ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwantedSpace : _root_.ThreeSum.LightWantedSetup.space free M left right NL NR U M shift ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hoffWord : (_root_.ThreeSum.LightOriginalOffset.word M (NL+NR) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwantedWord : (_root_.ThreeSum.LightSourceResidues.word M M U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hNWord : ((NL+NR : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightOriginalOffset.space at hoffSpace; omega)).trans hw
  have hselected : _root_.ThreeSum.LightOriginalOffset.selected M (fun i => μ (a+i)) (fun j => μ (b+j)) NL NR=shift :=
    _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.selected_congr hleft hright
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 25) (by rfl : program[25]? = some (body 0 24))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.body _root_.ThreeSum.LightBalancedWanted.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (NL + NR : ℕ) ?_ ?_ ?_
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
  have ho := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.program_meets (d := d+1) (μ := μ)
    (a := a) (b := b) (nLeft := NL) (nRight := NR) (p := M) (N := NL+NR)
    (free := free) (U := U) hw ha hb (by omega) (by omega) hoffSpace hoffWord (by omega)
    (fun i hi => by rw [hleft i hi]; exact hvaluesL i hi)
    (fun j hj => by rw [hright j hj]; exact hvaluesR j hj)).append
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program.map (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.relocate 13))).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.body 0 24]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ho _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ho ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro chosen μ₁ ⟨hchosen, hkeepO⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hchosenShift : chosen=(shift : ℤ) := hchosen.trans (congrArg Nat.cast hselected)
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostRelocation.meets
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedSetup.program_meets (d := d+1) (μ := μ₁) (a := a) (b := b)
      (NL := NL) (NR := NR) (M := M) (free := free) (U := U) (D := M) (shift := shift)
      left right hw hM ha hb hwantedSpace hwantedWord hshiftAbs (by omega)
      (fun i hi => (hkeepO _ (by omega)).trans (hleft i hi))
      (fun j hj => (hkeepO _ (by omega)).trans (hright j hj)) hvaluesL hvaluesR)
    _root_.ThreeSum1960614.Machine.ThreeSum.LightOriginalOffset.program).append [_root_.ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.body 0 24]
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hchosenShift, shift]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hchosenShift, shift] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hchosenShift, shift] <;> omega)
     on_goal -1 => (rintro result ν ⟨hresult, houtput, hkeepS⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hresult,houtput,?_,?_⟩
  · change M*(ν free).toNat ≤ NL*NR
    rw [houtput.1,Int.toNat_natCast]
    exact _root_.ThreeSum1960614.Machine.ThreeSum.WantedResidueKeys.selected_total_bound M left right NL NR
  · intro i hi
    exact (hkeepS i hi).trans (hkeepO i hi)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program_meets__implementation_22acf72a44) := (@ThreeSum1960614.Machine.ThreeSum.LightBalancedWanted.program_meets__implementation_22acf72a44)

#print axioms solution
