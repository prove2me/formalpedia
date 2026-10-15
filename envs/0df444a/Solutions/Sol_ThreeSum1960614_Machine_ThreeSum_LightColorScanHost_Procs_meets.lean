-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:07:31.777335+00:00
-- url     : https://prove2.me/submissions/a64be85e-93f0-494e-91cc-ea1e3ac599bc

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
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
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
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorScan_Procs_meets
import Theorems.Thm_ThreeSum_ColorClassLists_reduction_correct
import Theorems.Thm_ThreeSum_ColorParameters_index_lt

local instance platformRadixNonzero_2eb244d08c (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.ColorScan
end ThreeSum.ColorScan
namespace ThreeSum.LightColorParametersCosts
end ThreeSum.LightColorParametersCosts
namespace ThreeSum.LightColorScanHost
end ThreeSum.LightColorScanHost
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.ColorScan
end ThreeSum1960614.Machine.ThreeSum.ColorScan
namespace ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
end ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
end ThreeSum1960614.Machine.ThreeSum.LightColorScanHost
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds

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
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters
open _root_.ThreeSum.ColorParameters
























theorem parameter_index {W : ℕ} (p : _root_.ThreeSum.Coloring.Parameter W) : _root_.ThreeSum.ColorParameters.parameter (_root_.ThreeSum.ColorParameters.index_lt p)=p := by
  have hw : 0 < W := by have := p.1.1.isLt; omega
  have h0 := (p.2 (false,false)).isLt
  have h1 := (p.2 (false,true)).isLt
  have h2 := (p.2 (true,false)).isLt
  have h3 := (p.2 (true,true)).isLt
  have hq : _root_.ThreeSum.ColorParameters.index p/81=p.1.1.val*W+p.1.2.val := by unfold _root_.ThreeSum.ColorParameters.index; omega
  have hi : _root_.ThreeSum.ColorParameters.index p/81/W=p.1.1.val := by
    rw [hq,Nat.add_comm,Nat.add_mul_div_right _ _ hw,Nat.div_eq_of_lt p.1.2.isLt]
    simp
  have hj : _root_.ThreeSum.ColorParameters.index p/81%W=p.1.2.val := by
    rw [hq,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt p.1.2.isLt]
  apply Prod.ext
  · exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  · funext xy
    rcases xy with ⟨x,y⟩
    cases x <;> cases y <;> apply Fin.ext <;> dsimp [_root_.ThreeSum.ColorParameters.parameter,_root_.ThreeSum.ColorParameters.colorMap] <;> unfold _root_.ThreeSum.ColorParameters.index <;> omega





theorem reduction_correct {n W : ℕ} (x : Fin n→ℤ) (hn : n ≤ 2^W) :
    _root_.ThreeSum.Coloring.DistinctZeroSum x ↔
      ∃ t, ∃ ht : t < _root_.ThreeSum.ColorParameters.count W, _root_.ThreeSum.ColorClassLists.witness (_root_.ThreeSum.ColorParameters.parameter ht) x := by
  rw [_root_.ThreeSum.ColorClassLists.reduction_correct x hn]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨_root_.ThreeSum.ColorParameters.index p,_root_.ThreeSum.ColorParameters.index_lt p,by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters.parameter_index] using hp⟩
  · rintro ⟨t,ht,hp⟩
    exact ⟨_root_.ThreeSum.ColorParameters.parameter ht,hp⟩

end ThreeSum.ColorParameters

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Correctness of a prefix of the literal coloring family -/

namespace ThreeSum.ColorScan
open _root_.ThreeSum.ColorScan


open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters









theorem hit_complete {n W : ℕ} (x : Fin n → ℤ) (hn : n ≤ 2^W) :
    _root_.ThreeSum.ColorScan.Hit x W (_root_.ThreeSum.ColorParameters.count W) ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters.reduction_correct x hn]
  constructor
  · rintro ⟨i,hi,_,hx⟩
    exact ⟨i,hi,hx⟩
  · rintro ⟨i,hi,hx⟩
    exact ⟨i,hi,hi,hx⟩

end ThreeSum.ColorScan

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Finite and asymptotic cost of executing the small coloring family -/

namespace ThreeSum.LightColorParametersCosts
open _root_.ThreeSum.LightColorParametersCosts


open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds



theorem width_sufficient (n : ℕ) : n ≤ 2^_root_.ThreeSum.LightColorParametersCosts.width n := Nat.lt_log2_self.le









open _root_.Filter
open _root_.Real
open scoped _root_.Topology

noncomputable section









end
end ThreeSum.LightColorParametersCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorScanHost
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.LightColorParametersCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs.meets__implementation_2f00b55f9b {pMain src n params free colorTime colorDepth d : ℕ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs P pMain) (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : free+6 ≤ lim.space) (hsrc : src ≤ free) (hparams : params < free)
    (hword : (_root_.ThreeSum.LightColorScanHost.word n : ℤ) ≤ lim.word)
    (hd : d+_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)+colorDepth+4 ≤ lim.depth)
    (hread : μ params=(_root_.ThreeSum.Scales.inputBits n : ℤ))
    (hcolor : ∀ (i : ℕ) (hi : i < _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)) (ν : ℕ → ℤ),
      _root_.ThreeSum1960614.Machine.Light.Kept μ ν free → _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum.ColorParameters.fields (_root_.ThreeSum.ColorParameters.parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P R.scan.pColor dd [src,n,params,free,free+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ _root_.ThreeSum.ColorClassLists.witness (_root_.ThreeSum.ColorParameters.parameter hi) x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ free)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,params,free] μ (_root_.ThreeSum.LightColorScanHost.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧
        (r=1 ↔ _root_.ThreeSum.Coloring.DistinctZeroSum x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ξ free) := by
  have hWpos : 0 < _root_.ThreeSum.LightColorParametersCosts.width n := by unfold _root_.ThreeSum.LightColorParametersCosts.width; omega
  have hprod : 81*_root_.ThreeSum.LightColorParametersCosts.width n ≤ _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n) := by
    unfold _root_.ThreeSum.ColorParameters.count
    have hh := Nat.le_mul_of_pos_right (_root_.ThreeSum.LightColorParametersCosts.width n) hWpos
    nlinarith
  have hcount : (_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightColorScanHost.word; omega)).trans hword
  have hprodWord : (81 : ℤ)*(_root_.ThreeSum.LightColorParametersCosts.width n : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast hprod : (81 : ℤ)*(width n : ℤ) ≤ (count (width n) : ℤ)).trans hcount
  have hfull : (81 : ℤ)*(_root_.ThreeSum.LightColorParametersCosts.width n : ℤ)*(_root_.ThreeSum.LightColorParametersCosts.width n : ℤ)=(_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n) : ℤ) := by
    simp only [_root_.ThreeSum.ColorParameters.count,pow_two,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hbits : (_root_.ThreeSum.Scales.inputBits n : ℤ)+1=(_root_.ThreeSum.LightColorParametersCosts.width n : ℤ) := by simp [_root_.ThreeSum.LightColorParametersCosts.width]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.body _root_.ThreeSum.LightColorScanHost.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightColorParametersCosts.width n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, hbits, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hread, hbits, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, hbits, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hfull, hprodWord, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hfull, hprodWord, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hfull, hprodWord, _root_.ThreeSum.LightColorScanHost.word, _root_.ThreeSum.LightColorScan.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hs := R.scan.meets x μ hw hspace hsrc hparams.le hword hcolor
    (d := d+1) (t := _root_.ThreeSum.ColorParameters.count (_root_.ThreeSum.LightColorParametersCosts.width n)) (ν := μ) le_rfl (by omega) _root_.ThreeSum1960614.Machine.Light.SameOn.refl
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightColorScan.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time] <;> omega)
     on_goal -1 => (rintro result ξ ⟨hbool, hresult, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  exact ⟨hbool,hresult.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ColorScan.hit_complete x (_root_.ThreeSum1960614.Machine.ThreeSum.LightColorParametersCosts.width_sufficient n)),hkeep⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs.meets__implementation_2f00b55f9b) := (@ThreeSum1960614.Machine.ThreeSum.LightColorScanHost.Procs.meets__implementation_2f00b55f9b)

#print axioms solution
