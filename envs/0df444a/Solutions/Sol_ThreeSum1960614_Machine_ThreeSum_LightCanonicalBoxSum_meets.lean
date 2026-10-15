-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:25:42.526672+00:00
-- url     : https://prove2.me/submissions/ca94e232-bca8-4c35-9db6-ed7c3349d14f

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sublists
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
import Mathlib.Tactic.Push
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBoxSum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryEnumeration_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBoxSum
end ThreeSum.LightBoxSum
namespace ThreeSum.LightCanonicalBoxSum
end ThreeSum.LightCanonicalBoxSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBoxSum
end ThreeSum1960614.Machine.ThreeSum.LightBoxSum
namespace ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum
end ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
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
# Summing the canonical boxes of a sparse query

The missing-subset masks are loaded from an actual array, and every
summand is produced by the verified box-query procedure. Signed
accumulator bounds follow from bounds on the original leaf weights.
The final theorem identifies the sum with the canonical powerset-card
sum whenever the mask array is an exact enumeration of that family.
-/

namespace ThreeSum.LightBoxSum
open _root_.ThreeSum.LightBoxSum


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

























theorem sum_eq_canonical {L t : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (hn : missing.Nodup)
    (hmem : ∀ U, U ∈ missing ↔ U ∈ Q.powersetCard t) :
    (missing.map (_root_.ThreeSum.LightBoxSum.boxValue Q weight)).sum =
      ∑ U ∈ Q.powersetCard t, _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight := by
  have he : missing.toFinset = Q.powersetCard t := by
    ext U
    simpa using hmem U
  rw [← List.sum_toFinset (_root_.ThreeSum.LightBoxSum.boxValue Q weight) hn,he]
  rfl



end ThreeSum.LightBoxSum

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]

theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he



















theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).Nodup := by
  unfold _root_.ThreeSum.QueryCoordinates.missingSets
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.setLayer_nodup _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp ha
  have hbs := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,_root_.ThreeSum.QueryCoordinates.positions_toFinset] at has hbs
  have h := congrArg _root_.ThreeSum.SubsetAddress.natPositions he
  rw [_root_.ThreeSum.QueryCoordinates.decode_maskOf (has.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q)),
      _root_.ThreeSum.QueryCoordinates.decode_maskOf (hbs.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q))] at h
  exact h

@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightCanonicalBoxSum
open _root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.meets__implementation_dccbbf6e7c {pMain pEnum pSum : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.body pEnum pSum))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ}
    (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hdata : base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+Q.card.choose t ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t*(2^W*B) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hflags : Q.card-t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d+W+8 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [W,cut,Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,base,maskBase,work] μ (_root_.ThreeSum.LightCanonicalBoxSum.time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (Q.card.choose t)) := by
  have henumSpace : work+(2*W+2) ≤ lim.space := by
    unfold _root_.ThreeSum.LightPascal.tableSize at hspace
    nlinarith
  have henumWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hm : (2^(W+1) : ℕ) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hm : ((2^(W+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.body _root_.ThreeSum.LightCanonicalBoxSum.time
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets (d := d+1) (μ := μ) C.enumerate C.weights C.table.powers C.erase C.core
    Q hw henumSpace henumWord ht hmasks (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time] <;> omega)
     on_goal -1 => (rintro count μ₁ ⟨hcount, hmaskSeg, _, hkeepEnum⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hstored₁ : _root_.ThreeSum.LightBoxStages.StoredThrough μ₁ base cut weight W := by
    intro j hj S hS
    have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
    have ha : _root_.ThreeSum.LightBoxStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S < maskBase := by
      unfold _root_.ThreeSum.LightBoxStages.stageBase
      simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
      omega
    exact (hkeepEnum _ ⟨by omega,Or.inl ha⟩).trans (hstored j hj S hS)
  have hvalid : ∀ U ∈ _root_.ThreeSum.QueryCoordinates.missingSets Q t, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut := by
    intro U hU
    have hu := (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q U t).mp hU
    refine ⟨hu.1,hu.2,?_⟩
    rw [Finset.card_sdiff_of_subset hu.1,hu.2]
    exact hflags
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum.meets (d := d+1) (μ := μ₁) C.sum C.box C.minimum C.lookup C.size C.address
    C.table C.offset C.erase Q (_root_.ThreeSum.QueryCoordinates.missingSets Q t) weight hw hcut (by omega)
    (by simpa using hmasks) hspace hword (by simpa using haccWord)
    hvalid hweight hstored₁ hmaskSeg (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time, hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time, hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightQueryEnumeration.time, _root_.ThreeSum.LightBoxSum.time, hcount, _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length] <;> omega)
     on_goal -1 => (rintro res μ₂ ⟨hres, hkeepSum⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,?_⟩
  · exact hres.trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBoxSum.sum_eq_canonical Q weight (_root_.ThreeSum.QueryCoordinates.missingSets Q t)
      (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup Q t) (fun U => by simp only [_root_.ThreeSum.QueryCoordinates.missingSets_mem,Finset.mem_powersetCard]))
  · intro i hi
    exact (hkeepSum i hi.1).trans (hkeepEnum i hi)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.meets__implementation_dccbbf6e7c) := (@ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.meets__implementation_dccbbf6e7c)

#print axioms solution
