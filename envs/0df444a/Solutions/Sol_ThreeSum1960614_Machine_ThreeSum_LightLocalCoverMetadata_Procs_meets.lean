-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:53.528414+00:00
-- url     : https://prove2.me/submissions/24c58384-6f2e-4feb-8665-3e528399831a

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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Range
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_log2_meets
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets

private theorem platform_seg_cons_e4c96c1326 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_e4c96c1326 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_e4c96c1326 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata
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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











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















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (x : ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  platform_seg_append_e4c96c1326.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [platform_seg_cons_e4c96c1326]⟩



theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl



/-- Writing inside the region. -/
theorem SameOutside.update (h : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc





































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum.LightLocalCoverLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables

















theorem work_le_space (base h : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h := by
  have hm := Nat.le_max_left
    (_root_.ThreeSum.LightLocalCoverCandidate.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)))
  change _root_.ThreeSum.LightLocalCoverCandidate.space (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h at hm
  unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hm
  omega

theorem schedule_end_le_space (base h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h := Nat.le_max_right ..



end ThreeSum.LightLocalCoverLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup renaming word -> word
set_option maxHeartbeats 2000000
set_option maxRecDepth 8500
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.Procs.meets__implementation_045ab95839 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.Procs P pMain)
    {μ : ℕ → ℤ} {base h dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 ≤ lim.depth)
    (hout : dst+12 ≤ base)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.space base h ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h,base,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time h)
      (fun r ν => r = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values base h) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst 12) := by
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hbuildWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have h1024Word := hbudget 1024 (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hLWord := hbudget (464*h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hNWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hTWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hcolsWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hlogWord := hbudget (2*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h+2) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega)
  have hhostLe : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h := by
    have hfirst : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word h := Nat.le_add_right ..
    have hsecond : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverBuild.word h ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word h := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word; omega
    exact hfirst.trans hsecond
  have hcoreBudget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    hbudget x (hx.trans hhostLe)
  have hwidthWord := hcoreBudget (2*(464*h)) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightWeightGather.word
    omega)
  have hnWord := hcoreBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word
      _root_.ThreeSum.LightPairFlags.word _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices
    omega)
  have hpWord := hcoreBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word
      _root_.ThreeSum.LightPairFlags.word
    omega)
  have hcapWord := hcoreBudget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word
      _root_.ThreeSum.LightPairFlags.word
    omega)
  have hwidthWordZ : (2 : ℤ)*(464*(h : ℤ)) ≤ lim.word := by exact_mod_cast hwidthWord
  have hLWordZ : (464 : ℤ)*h ≤ lim.word := by exact_mod_cast hLWord
  have hp2WordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_mul] using hcolsWord
  have hcolsEq : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h : ℤ) = (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_mul]
  have hp2Nonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by positivity
  have hlogBound : Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h := by
    rw [Nat.log2_eq_log_two]
    exact (Nat.log_le_self 2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2)).trans (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,pow_two])
  have hlogResultWord : ((Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2)+1 : ℕ) : ℤ) ≤ lim.word := by
    apply hbudget
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSetup.word
    omega
  have hscale : 320*(2*h+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by
    change 320*(2*h+1) ≤ 320*(2*h+1)*(Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2)+1)
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hscaleWord : ((320*(2*h+1) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hscale).trans hTWord
  have hscaleWordZ : (320 : ℤ)*(2*(h : ℤ)+1) ≤ lim.word := by exact_mod_cast hscaleWord
  have hroundWordZ : (320 : ℤ)*(2*(h : ℤ)+1)*(Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2)+1) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize,_root_.ThreeSum.LocalHashMoments.scheduleLength,Nat.cast_mul,Nat.cast_add,Nat.cast_one,
      Nat.cast_ofNat] using hTWord
  have hroundNonneg : (0 : ℤ) ≤ 320*(2*(h : ℤ)+1)*(Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2)+1) := by positivity
  have hworkSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h ≤ lim.space := (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work_le_space base h).trans hspace
  have hschedSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ lim.space :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.schedule_end_le_space base h).trans hspace
  have hsmall (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (hx.trans hworkSpace)).trans hw
  have hbitPtr := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr base h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps
    omega)
  have hmaps := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0; omega)
  have hraw0 := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1; omega)
  have hraw1 := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0; omega)
  have hhist0 := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1; omega)
  have hhist1 := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr; omega)
  have hmatrix := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work; omega)
  have hwork := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h) le_rfl
  have hbase := hsmall base (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr; omega)
  have hprodBits := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h*(464*h)) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps
    omega)
  have hprodRows := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h))) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0
    omega)
  have hprodRaw := hsmall (2*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0; omega)
  have hprodHist := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1; omega)
  have hprodMatrix := hsmall (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work; omega)
  have hprodBitsZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h : ℤ)*(464*(h : ℤ)) ≤ lim.word := by exact_mod_cast hprodBits
  have hprodRowsZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*(2*(464*(h : ℤ))) ≤ lim.word := by exact_mod_cast hprodRows
  have hprodHistZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ lim.word := by exact_mod_cast hprodHist
  have hprodMatrixZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_mul] using hprodMatrix
  have hbitPtrZ : (base : ℤ)+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr,Nat.cast_add] using hbitPtr
  have hmapsZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h : ℤ)*(464*(h : ℤ)) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hmaps
  have hraw0Z : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*(2*(464*(h : ℤ))) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw0
  have hraw1Z : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 base h : ℤ)+2*(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hraw1
  have hhist0Z : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 base h : ℤ)+2*(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hhist0
  have hhist1Z : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1,Nat.cast_add,Nat.cast_mul] using hhist1
  have hmatrixZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr,Nat.cast_add,Nat.cast_mul] using hmatrix
  have hworkZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_add,Nat.cast_mul] using hwork
  have hbitsNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.vertices h : ℤ)*(464*(h : ℤ)) := by positivity
  have hrowsNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*(2*(464*(h : ℤ))) := by positivity
  have hhistNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by positivity
  have hmatrixNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)*((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) := by positivity
  have hscheduleWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : scheduleMaps base h ≤ lim.space)).trans hw
  have hscheduleWordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ)+
      (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps,_root_.ThreeSum.LightCoverGreedy.total,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_add,Nat.cast_mul,
      Int.add_assoc] using hscheduleWord
  have hscheduleWork : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h = _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum.LightCoverGreedy.total
    omega

  have hbaseSpace : base ≤ lim.space := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr at hworkSpace
    omega
  have hcandidateSpace : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h ≤ lim.space := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates _root_.ThreeSum.LightCoverGreedy.out _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps _root_.ThreeSum.LightCoverGreedy.total at *
    omega
  have hcandidateWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hcandidateSpace).trans hw
  have hcandidateWordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h+(_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates,_root_.ThreeSum.LightCoverGreedy.out,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols,Nat.cast_add,Nat.cast_mul] using hcandidateWord
  have hnextWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hschedSpace).trans hw
  have hnextWordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(2*(464*(h : ℤ))) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hnextWord
  have hproductWordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(2*(464*(h : ℤ))) ≤ lim.word := by
    have hm : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ lim.space := by omega
    exact (by exact_mod_cast hm : (scheduleSize h : ℤ)*(2*(464*(h : ℤ))) ≤ lim.space).trans hw
  have hproductNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(2*(464*(h : ℤ))) := by positivity
  have htwoWord : ((2*h : ℕ) : ℤ) ≤ lim.word := by omega
  have htwoWordZ : (2 : ℤ)*h ≤ lim.word := by exact_mod_cast htwoWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.body _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (464 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 * (464 * h) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hpowers : ∀ e ≤ 2*(464*h), (((_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^e : ℕ) : ℤ) ≤ lim.word := by
    intro e he
    have hp : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)^e ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := Nat.pow_le_pow_right (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) he
    exact (Int.ofNat_le.mpr hp).trans hNWord
  have hpower := _root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d+1) (b := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (e := 2*(464*h))
    S.power μ hwidthWord hpowers
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpower _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpower ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
     on_goal -1 => (rintro vc μ₁ ⟨hvc, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  have hvc' : vc = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℤ) := hvc
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hl := _root_.ThreeSum1960614.Machine.Light.log2_meets (d := d+1) (x := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) S.log μ hlogWord
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
     on_goal -1 => (rintro vl μ₂ ⟨hvl, hmem₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  have hvl' : vl = (Nat.log2 (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h^2) : ℤ) := by
    simpa only [Nat.log2_eq_log_two,pow_two,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] using hvl
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvl', _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize, _root_.ThreeSum.LocalHashMoments.scheduleLength]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvl', _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize, _root_.ThreeSum.LocalHashMoments.scheduleLength] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvl', _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize, _root_.ThreeSum.LocalHashMoments.scheduleLength] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.bitPtr] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0, hvc']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0, hvc'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw0, hvc'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.raw1] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1, hvc']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1, hvc'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1, hvc'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr, hvc']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr, hvc'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr, hvc'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.work, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hscheduleWork, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hscheduleWork, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hscheduleWork, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates, _root_.ThreeSum.LightCoverGreedy.out, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates, _root_.ThreeSum.LightCoverGreedy.out, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates, _root_.ThreeSum.LightCoverGreedy.out, hvc', _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (464 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (2 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 2) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 3) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvc']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvc'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time, hvc'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 4) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 5) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 6) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 7) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 8) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 9) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 10) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 11) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,?_,?_⟩
  · have hn : _root_.ThreeSum1960614.Machine.Light.Seg μ dst [] := _root_.ThreeSum1960614.Machine.Light.Seg.nil
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.values] using
      ((((((((((((hn.snoc (464*h : ℕ)).snoc (2*h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℕ)).snoc
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h : ℕ)).snoc
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h : ℕ)).snoc
        (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℕ)).snoc (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h : ℕ))
  · have hp : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ dst 12 := _root_.ThreeSum1960614.Machine.Light.SameOutside.refl
    exact ((((((((((((hp.update (by omega : dst ≤ dst ∧ dst < dst+12) (464*h : ℕ)).update
      (by omega : dst ≤ dst+1 ∧ dst+1 < dst+12) (2*h : ℕ)).update
      (by omega : dst ≤ dst+2 ∧ dst+2 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℕ)).update
      (by omega : dst ≤ dst+3 ∧ dst+3 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h : ℕ)).update
      (by omega : dst ≤ dst+4 ∧ dst+4 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.scheduleMaps base h : ℕ)).update
      (by omega : dst ≤ dst+5 ∧ dst+5 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.candidates base h : ℕ)).update
      (by omega : dst ≤ dst+6 ∧ dst+6 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist0 base h : ℕ)).update
      (by omega : dst ≤ dst+7 ∧ dst+7 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.hist1 base h : ℕ)).update
      (by omega : dst ≤ dst+8 ∧ dst+8 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.maps base h : ℕ)).update
      (by omega : dst ≤ dst+9 ∧ dst+9 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverLayout.matrixPtr base h : ℕ)).update
      (by omega : dst ≤ dst+10 ∧ dst+10 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.nextFree base h : ℕ)).update
      (by omega : dst ≤ dst+11 ∧ dst+11 < dst+12) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h : ℕ))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.Procs.meets__implementation_045ab95839) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverMetadata.Procs.meets__implementation_045ab95839)

#print axioms solution
