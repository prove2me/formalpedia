-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:04.535645+00:00
-- url     : https://prove2.me/submissions/63c2f9e1-e376-43d9-9611-c78e4fe9e51c

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
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
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetSize_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaPass_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le
import Theorems.Thm_ThreeSum_Subset_partialZeta_insert

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.Subset
end ThreeSum.Subset
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.SubsetStages
end ThreeSum.SubsetStages
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.Subset
end ThreeSum1960614.Machine.ThreeSum.Subset
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetStages
end ThreeSum1960614.Machine.ThreeSum.SubsetStages

namespace ThreeSum1960614.Machine

/-!
# Exact subset identities used by the proposed 3SUM algorithm

This module proves the algebraic identities, rather than taking the claimed
algorithm or its running time as an assumption.  `zeta` is the ordinary finite
subset sum; `mobius` is its signed inverse.  The fixed-cardinality specialization
is the identity used by the repeated histogram construction.
-/

namespace ThreeSum.Subset
open _root_.ThreeSum.Subset


open scoped _root_.BigOperators

variable {α : Type*} [DecidableEq α]



































/-! ## Stored partial zeta stages -/





theorem partialZeta_empty (f : Finset α → ℤ) (u : Finset α) :
    _root_.ThreeSum.Subset.partialZeta ∅ f u = f u := by
  simp [_root_.ThreeSum.Subset.partialZeta]























/-! ## Prefix reporting mass -/











end ThreeSum.Subset

end ThreeSum1960614.Machine

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
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Canonical suffix stages of a compact zeta table

Stage `j` has processed exactly the last `j` coordinates. Advancing one
stage is one ordinary zeta pass. Every value and every predecessor used
by these stages remains inside the same cardinality downset.
-/

namespace ThreeSum.SubsetStages
open _root_.ThreeSum.SubsetStages


open _root_.Finset



@[simp] theorem mem_suffix {L j : ℕ} (a : Fin L) : a ∈ _root_.ThreeSum.SubsetStages.suffix L j ↔ L-j ≤ a.val := by
  simp [_root_.ThreeSum.SubsetStages.suffix]

@[simp] theorem suffix_zero (L : ℕ) : _root_.ThreeSum.SubsetStages.suffix L 0 = ∅ := by
  ext a
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.mem_suffix,Nat.sub_zero,not_le,Finset.notMem_empty,iff_false]
  exact a.isLt





theorem nextCoord_not_mem {L j : ℕ} (hj : j < L) : _root_.ThreeSum.SubsetStages.nextCoord j hj ∉ _root_.ThreeSum.SubsetStages.suffix L j := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.mem_suffix,_root_.ThreeSum.SubsetStages.nextCoord]
  omega

theorem suffix_succ {L j : ℕ} (hj : j < L) :
    _root_.ThreeSum.SubsetStages.suffix L (j+1) = insert (_root_.ThreeSum.SubsetStages.nextCoord j hj) (_root_.ThreeSum.SubsetStages.suffix L j) := by
  ext a
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.mem_suffix,Finset.mem_insert,Fin.ext_iff,_root_.ThreeSum.SubsetStages.nextCoord]
  omega



@[simp] theorem stageValue_zero {L : ℕ} (f : Finset (Fin L) → ℤ) : _root_.ThreeSum.SubsetStages.stageValue f 0 = f := by
  funext S
  simp [_root_.ThreeSum.SubsetStages.stageValue,_root_.ThreeSum1960614.Machine.ThreeSum.Subset.partialZeta_empty]

theorem stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    _root_.ThreeSum.SubsetStages.stageValue f (j+1) = _root_.ThreeSum.Subset.zetaStep (_root_.ThreeSum.SubsetStages.nextCoord j hj) (_root_.ThreeSum.SubsetStages.stageValue f j) := by
  funext S
  rw [_root_.ThreeSum.SubsetStages.stageValue,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.suffix_succ hj]
  exact _root_.ThreeSum.Subset.partialZeta_insert f S (_root_.ThreeSum.SubsetStages.suffix L j) (_root_.ThreeSum.SubsetStages.nextCoord j hj) (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.nextCoord_not_mem hj)







end ThreeSum.SubsetStages

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









end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetStages
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets__implementation_738bb3e8cd
    {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.body pSize pPass))
    (hSize : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (hPass : P[pPass]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ}
    (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,base,maskBase,work] μ (_root_.ThreeSum.LightZetaStages.time L cut)
      (fun _ μ' => _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f L ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase base ((L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut)) := by
  have hstage (i : ℕ) (hi : i ≤ L) :
      _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) i+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase := by
    have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (Nat.succ_le_succ hi)
    unfold _root_.ThreeSum.LightZetaStages.stageBase
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  have hfirst := hstage 0 (by omega)
  simp only [_root_.ThreeSum.LightZetaStages.stageBase,Nat.zero_mul,Nat.add_zero] at hfirst
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.body _root_.ThreeSum.LightZetaStages.time
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets (d := d+1) (μ := μ)
    hSize C hOffset hw hspace hword hcut (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetSize.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetSize.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetSize.time] <;> omega)
     on_goal -1 => (rintro cap μ₁ ⟨hcap, hsizeKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst cap
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.Inv μ cut base maskBase work f) L
    (_root_.ThreeSum.LightZetaPass.time L cut+50) ?start ?round ?done ?bound
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetSize.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightDownsetSize.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))))
  case start =>
    refine ⟨0,μ₁,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(L : ℤ),cut,base,maskBase,work,_root_.ThreeSum.SubsetAddress.downsetCap L cut,0] =
        _root_.Light.frame ([(L : ℤ),cut,base,maskBase,work,_root_.ThreeSum.SubsetAddress.downsetCap L cut,0] ++ [0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm
    · intro i hi
      have he : i = 0 := by omega
      subst i
      intro S hS
      have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
      simpa only [_root_.ThreeSum.LightZetaStages.stageBase,Nat.zero_mul,Nat.add_zero,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.stageValue_zero] using
        (hsizeKept _ (by omega)).trans (hread S hS)
    · intro i hi
      exact hsizeKept i (by omega)
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hstored,hkept⟩
    have hsource := hstored j le_rfl
    have hsrc := hstage j (by omega)
    have hdst := hstage (j+1) (by omega)
    have hsep : _root_.Light.Apart (_root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) j) (_root_.ThreeSum.SubsetAddress.downsetCap L cut)
        (_root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (j+1)) (_root_.ThreeSum.SubsetAddress.downsetCap L cut) := by
      left
      simp [_root_.ThreeSum.LightZetaStages.stageBase,Nat.add_mul,Nat.add_assoc]
    have hcurrentValues := _root_.ThreeSum.SubsetStages.stageValue_abs_le f hvalues j (Nat.le_of_lt hj)
    have hvalue : 2*(((2^j*U : ℕ) : ℤ)) ≤ lim.word := by
      have hp : (2^(j+1) : ℕ) ≤ 2^L := Nat.pow_le_pow_right (by decide) (by omega)
      have hu := Nat.mul_le_mul_right U hp
      have he : 2*(2^j*U) = 2^(j+1)*U := by rw [pow_succ]; ring
      have hh : (2*(2^j*U) : ℕ) ≤ 2^L*U := by rw [he]; exact hu
      exact (by exact_mod_cast hh : 2*(((2^j*U : ℕ) : ℤ)) ≤ ((2^L*U : ℕ) : ℤ)).trans hvalueWord
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaPass.meets (d := d+1) hPass hEnumSetup hEnum hBatch hCell
      C hOffset hErase (_root_.ThreeSum.SubsetStages.nextCoord j hj) (_root_.ThreeSum.SubsetStages.stageValue f j)
      hw hcut hsrc hdst hmasks hsep hspace hword hvalue hsource hcurrentValues (by omega)
    have hcoord : (L : ℤ)-1-(j : ℤ) = ((_root_.ThreeSum.SubsetStages.nextCoord j hj).val : ℤ) := by
      simp only [_root_.ThreeSum.SubsetStages.nextCoord]
      omega
    have hsrcCast : (base : ℤ)+(j : ℤ)*(_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) =
        (_root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) j : ℤ) := by
      simp [_root_.ThreeSum.LightZetaStages.stageBase]
    have hdstCast : (base : ℤ)+((j : ℤ)+1)*(_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) =
        (_root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (j+1) : ℤ) := by
      simp [_root_.ThreeSum.LightZetaStages.stageBase]
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.roundBody
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcoord, hsrcCast, hdstCast]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcoord, hsrcCast, hdstCast] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcoord, hsrcCast, hdstCast] <;> omega)
       on_goal -1 => (rintro res μ₂ ⟨hnew, hpassKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,res,μ₂,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro i hi
      by_cases heq : i = j+1
      · subst i
        simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.stageValue_succ f hj] using hnew
      · have hij : i ≤ j := by omega
        have himul := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap L cut) hij
        intro S hS
        have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
        have hbefore : _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) i+_root_.ThreeSum.SubsetAddress.subsetRank S <
            _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (j+1) := by
          unfold _root_.ThreeSum.LightZetaStages.stageBase
          simp only [Nat.add_mul,Nat.one_mul]
          omega
        have hiend := hstage i (by omega)
        exact (hpassKept _ ⟨by omega,Or.inl hbefore⟩).trans (hstored i hij S hS)
    · intro i hi
      have hnextLow : base ≤ _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (j+1) := by
        unfold _root_.ThreeSum.LightZetaStages.stageBase
        omega
      have hnextHigh := hstage (j+1) (by omega)
      have hmul := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (show j+2 ≤ L+1 by omega)
      have hnextEnd : _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap L cut) (j+1)+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤
          base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut := by
        unfold _root_.ThreeSum.LightZetaStages.stageBase
        simp only [Nat.add_mul,Nat.one_mul] at hmul ⊢
        omega
      exact (hpassKept i ⟨hi.1,by omega⟩).trans (hkept i hi)
  case done =>
    rintro _ _ ⟨r,μ',rfl,hstored,hkept⟩
    exact ⟨hstored,hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets__implementation_738bb3e8cd) := (@ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets__implementation_738bb3e8cd)

#print axioms solution
