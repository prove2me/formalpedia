-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:35:18.121663+00:00
-- url     : https://prove2.me/submissions/647e842f-9d3f-4e88-aec7-c6bdc6ee94b7

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
import Mathlib.Algebra.Order.Ring.Nat
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceRetainedHost_Procs_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightBlockSourceBatchStep
end ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000











@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum.LightBlockSourceBatchLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem left_ge_slot (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0
  omega

theorem right_ge_left (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i := Nat.le_add_right _ _

theorem right_end (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut = _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.stride
  ring

theorem right_end_le_masks {base count W cut i : ℕ} (hi : i < count) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_mono base count W cut (by omega)





theorem slot_width_le_work {base count W cut i : ℕ} (hi : i < count) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i+W ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end_le_masks (base := base) (W := W) (cut := cut) hi
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 _root_.ThreeSum.LightBlockSourceBatchLayout.family at hr
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase
  omega

theorem header_end_le_slot {base count W cut i : ℕ} (hi : i < count) :
    base+2*i+2 ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
  omega

theorem masks_le_work (base count W cut : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count W cut ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase
  omega

theorem addresses_le_work {base count W cut i : ℕ} (hi : i < count) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.flags base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut ∧
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have he := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end_le_masks hi).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.masks_le_work base count W cut)
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 at he ⊢
  omega











theorem banks_le_left_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S := by
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_ge_slot base count W cut i)
  unfold _root_.ThreeSum.LightZetaStages.stageBase
  omega

theorem banks_le_right_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S := by
  have hs := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_ge_slot base count W cut i)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_ge_left base count W cut i)
  unfold _root_.ThreeSum.LightZetaStages.stageBase
  omega

end ThreeSum.LightBlockSourceBatchLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets__implementation_5d7e86e221 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      base count i : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+10 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h)) (hi : i < count)
    (hocc : occ+J ≤ base) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hsourceHistL : sourceHistL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hsourceHistR : sourceHistR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (_root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut) h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,count,
        _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count,_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base count (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut,i]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.time h J cut) (fun _ ν =>
        _root_.ThreeSum.LightZetaStages.StoredThrough ν (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i) cut
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i) cut
          (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(464*h)) ∧
        ν (base+2*i) = (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i : ℤ) ∧
        ν (base+2*i+1) = (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut i) (base+2*i) 2) := by
  have hs : _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut+(J*(464*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hwork : _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut ≤ lim.space := by omega
  have hslot := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_width_le_work (base := base) (W := J*(464*h)) (cut := cut) hi
  have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.header_end_le_slot (base := base) (W := J*(464*h)) (cut := cut) hi
  have hbanks := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count (J*(464*h)) cut i
  have haddr := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.addresses_le_work (base := base) (W := J*(464*h)) (cut := cut) hi
  have hwidth : (J : ℤ)*(464*(h : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show J*(464*h) ≤ lim.space by omega) :
      (J : ℤ)*(464*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(464*(h : ℤ)) := by positivity
  have hwidthPlus : (J : ℤ)*(464*(h : ℤ))+1 ≤ lim.word :=
    (by exact_mod_cast (show J*(464*h)+1 ≤ lim.space by omega) :
      (J : ℤ)*(464*(h : ℤ))+1 ≤ lim.space).trans hw
  have hleftSpace : _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i ≤ lim.space := by omega
  have hrightSpace : _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i ≤ lim.space := by omega
  have hprodNat : i*_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut ≤ lim.space := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.slot at hslot
    omega
  have hprod : (i : ℤ)*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprodNat :
      (i : ℤ)*(LightBlockSourceBatchLayout.stride (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut : ℤ) := by positivity
  have htwocapNat : 2*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase at hleftSpace
    omega
  have htwocap : (2 : ℤ)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast htwocapNat : (2 : ℤ)*(downsetCap (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  have hfamNat : (J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.family at hrightSpace
    omega
  have hfam : ((J : ℤ)*(464*(h : ℤ))+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hfamNat : ((J : ℤ)*(464*(h : ℤ))+1)*(downsetCap (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  have hfamNonneg : (0 : ℤ) ≤ ((J : ℤ)*(464*(h : ℤ))+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) := by positivity
  have hbase : base ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut i := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hbanks
    omega
  have hs0 : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count+
      i*_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut ≤ lim.space := by
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.slot at hslot
    omega
  have hs1 : _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut i+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := haddr.1.trans hwork
  have hs2 : _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 base count (J*(464*h)) cut i+
      J*(464*h) ≤ lim.space := haddr.2.1.trans hwork
  have hs3 : _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 base count (J*(464*h)) cut i+
      J*(464*h) ≤ lim.space := haddr.2.2.1.trans hwork
  have hs4 : _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft base count (J*(464*h)) cut i+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := haddr.2.2.2.1.trans hwork
  have hs5 : _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight base count (J*(464*h)) cut i+
      _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := haddr.2.2.2.2.1.trans hwork
  have hs6 : _root_.ThreeSum.LightBlockSourceBatchLayout.flags base count (J*(464*h)) cut i+
      2*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+2 ≤ lim.space := haddr.2.2.2.2.2.1.trans hwork
  have hs7 : _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i+
      (J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ lim.space := haddr.2.2.2.2.2.2.trans hwork
  have hs2Int : (_root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 base count (J*(464*h)) cut i : ℤ)+
      (J : ℤ)*(464*(h : ℤ)) ≤ lim.word := (by exact_mod_cast hs2 :
        (LightBlockSourceBatchLayout.coeff0 base count (J*(464*h)) cut i : ℤ)+
          (J : ℤ)*(464*(h : ℤ)) ≤ lim.space).trans hw
  have hs3Int : (_root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 base count (J*(464*h)) cut i : ℤ)+
      (J : ℤ)*(464*(h : ℤ)) ≤ lim.word := (by exact_mod_cast hs3 :
        (LightBlockSourceBatchLayout.coeff1 base count (J*(464*h)) cut i : ℤ)+
          (J : ℤ)*(464*(h : ℤ)) ≤ lim.space).trans hw
  have hs7Int : (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i : ℤ)+
      ((J : ℤ)*(464*(h : ℤ))+1)*(_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hs7 : (LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i : ℤ)+
      ((J : ℤ)*(464*(h : ℤ))+1)*(downsetCap (J*(464*h)) cut : ℤ) ≤ lim.space).trans hw
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.body _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.slot]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.slot] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.slot] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.coeff0] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.coeff1] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.rawRight base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.rawRight] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.flags base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.flags]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.flags] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.flags] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase, _root_.ThreeSum.LightBlockSourceBatchLayout.family]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase, _root_.ThreeSum.LightBlockSourceBatchLayout.family] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase, _root_.ThreeSum.LightBlockSourceBatchLayout.family] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hrun := C.source.meets (d := d+1) (μ := μ) (cut := cut) (p := p) (shift := shift)
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (sourceHistL := sourceHistL) (sourceHistR := sourceHistR)
    (masks := _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut i)
    (coeff0 := _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 base count (J*(464*h)) cut i)
    (coeff1 := _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 base count (J*(464*h)) cut i)
    (rawLeft := _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft base count (J*(464*h)) cut i)
    (rawRight := _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight base count (J*(464*h)) cut i)
    (flags := _root_.ThreeSum.LightBlockSourceBatchLayout.flags base count (J*(464*h)) cut i)
    (baseL := _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J*(464*h)) cut i)
    (baseR := _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J*(464*h)) cut i)
    (maskBase := _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count (J*(464*h)) cut)
    (bitBase := _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base count (J*(464*h)) cut)
    (rowOut := _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base count (J*(464*h)) cut)
    (work := _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut)
    B b A a q vL vR eL eR hw (by omega) hcut
    (hocc.trans hbase) (hmaps.trans hbase) (hcandidates.trans hbase)
    (hleft.trans hbase) (hright.trans hbase) (hsourceHistL.trans hbase) (hsourceHistR.trans hbase)
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end_le_masks hi)
    le_rfl le_rfl le_rfl hspace hword hinputL hinputR hhistReadL hhistReadR hoccRead hcover
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
     on_goal -1 => (rintro r ν ⟨storedL, storedR, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 2 * i) (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (base + 2 * i + 1) (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count (J * (464 * h)) cut i : ℕ) ?_ ?_ ?_
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
  dsimp only
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j hj S hS
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_left_cell base count (J*(464*h)) cut i j S
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact storedL j hj S hS
  · intro j hj S hS
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_right_cell base count (J*(464*h)) cut i j S
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact storedR j hj S hS
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self ..
  · intro x hx
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact kept x hx.1
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets__implementation_5d7e86e221.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.Procs.meets__implementation_5d7e86e221.{u_implementation_0,u_implementation_1})

#print axioms solution
