-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:14:17.229995+00:00
-- url     : https://prove2.me/submissions/d173341f-af2a-4a5d-ad31-2ab1809d2327

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskUnion_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSign_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightStageLookup_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSignedLeafGeneral
end ThreeSum.LightSignedLeafGeneral
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSignedLeafGeneral
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.meets__implementation_4333f95165 {pMain pUnion pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.body pUnion pLookup pSign))
    (hUnion : P[pUnion]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.body pPowers pErase))
    (hLookup : P[pLookup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.body pSize pAddress))
    (hSign : P[pSign]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.body)
    (hSize : P[pSize]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetAddress.body pSetup pOffset))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : (preL ∪ S).card ≤ cut) (hcardR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+6 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
        S.card,_root_.ThreeSum.SubsetAddress.subsetMask S,baseL,baseR,work] μ (_root_.ThreeSum.LightSignedLeafGeneral.time W)
      (fun r μ' => r = _root_.ThreeSum.SignedLeaf.value f g stage preL preR S ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by
  have hScard : S.card ≤ W := by simpa using Finset.card_le_univ S
  have hCL : (preL ∪ S).card ≤ W := hcardL.trans hcut
  have hCR : (preR ∪ S).card ≤ W := hcardR.trans hcut
  have hpowWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(W+1) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(W+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have haddrL : _root_.ThreeSum.LightStageLookup.readAddr cut baseL stage (preL ∪ S) < work := by
    have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hcardL
    have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hstage)
    unfold _root_.ThreeSum.LightStageLookup.readAddr
    simp only [Nat.succ_mul] at hm hdataL
    omega
  have haddrR : _root_.ThreeSum.LightStageLookup.readAddr cut baseR stage (preR ∪ S) < work := by
    have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hcardR
    have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hstage)
    unfold _root_.ThreeSum.LightStageLookup.readAddr
    simp only [Nat.succ_mul] at hm hdataR
    omega
  have hreadL : μ (_root_.ThreeSum.LightStageLookup.readAddr cut baseL stage (preL ∪ S)) =
      _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S) := by
    simpa only [_root_.ThreeSum.LightStageLookup.readAddr,_root_.ThreeSum.LightZetaStages.stageBase] using hstoredL stage hstage _ hcardL
  have hreadR : μ (_root_.ThreeSum.LightStageLookup.readAddr cut baseR stage (preR ∪ S)) =
      _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S) := by
    simpa only [_root_.ThreeSum.LightStageLookup.readAddr,_root_.ThreeSum.LightZetaStages.stageBase] using hstoredR stage hstage _ hcardR
  have hproduct : |_root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
      _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)| ≤ lim.word := by
    rw [abs_mul]
    have h₁ := _root_.ThreeSum.SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hcardL
    have h₂ := _root_.ThreeSum.SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hcardR
    have hh := mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)
    exact hh.trans (by simpa only [Nat.cast_mul] using hproductWord)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.body _root_.ThreeSum.LightSignedLeafGeneral.time
  have huL := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.meets (d := d+1) (μ := μ) (dst := work) (work := work+1)
    hUnion C.powers hErase preL S hw (by omega) (by omega) hpowWord (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (huL _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen huL ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro maskL μ₁ ⟨hmaskL, hcardReadL, hpowersL, hkeepUL⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepL₁ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₁ work := by
    intro i hi
    exact hkeepUL i ⟨by omega,Or.inl hi⟩
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((preL ∪ S).card : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcardReadL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcardReadL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcardReadL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hreadL₁ : μ₁ (_root_.ThreeSum.LightStageLookup.readAddr cut baseL stage (preL ∪ S)) =
      _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S) := (hkeepL₁ _ haddrL).trans hreadL
  have hcL := _root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.meets (d := d+1) (μ := μ₁) (work := work+1)
    hLookup hSize hAddress C hOffset (preL ∪ S) _ hw hcut (by omega) hspace hword hcardL hstage hreadL₁ (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcL _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcL ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmaskL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmaskL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmaskL, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro left μ₂ ⟨hleft, hkeepLR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepL₂ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₂ work := by
    intro i hi
    exact (hkeepLR i (by omega)).trans (hkeepL₁ i hi)
  have huR := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskUnion.meets (d := d+1) (μ := μ₂) (dst := work) (work := work+1)
    hUnion C.powers hErase preR S hw (by omega) (by omega) hpowWord (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (huR _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen huR ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro maskR μ₃ ⟨hmaskR, hcardReadR, hpowersR, hkeepUR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepR₁ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₃ work := by
    intro i hi
    exact (hkeepUR i ⟨by omega,Or.inl hi⟩).trans (hkeepL₂ i hi)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((preR ∪ S).card : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcardReadR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcardReadR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcardReadR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hreadR₁ : μ₃ (_root_.ThreeSum.LightStageLookup.readAddr cut baseR stage (preR ∪ S)) =
      _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S) := (hkeepR₁ _ haddrR).trans hreadR
  have hcR := _root_.ThreeSum1960614.Machine.ThreeSum.LightStageLookup.meets (d := d+1) (μ := μ₃) (work := work+1)
    hLookup hSize hAddress C hOffset (preR ∪ S) _ hw hcut (by omega) hspace hword hcardR hstage hreadR₁ (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcR _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcR ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmaskR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmaskR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmaskR, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro right μ₄ ⟨hright, hkeepRR⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkeepR₂ : _root_.ThreeSum1960614.Machine.Light.Kept μ μ₄ work := by
    intro i hi
    exact (hkeepRR i (by omega)).trans (hkeepR₁ i hi)
  have hpBound := abs_le.mp hproduct
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S) * _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hleft, hright, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hleft, hright, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hleft, hright, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hsign := _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.meets (d := d+1) (μ := μ₄) (e := S.card) hSign hw (by omega) hproduct
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hsign _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hsign ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightMaskUnion.time, _root_.ThreeSum.LightStageLookup.time, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro res μ₅ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₅
  exact ⟨hres,hkeepR₂⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.meets__implementation_4333f95165) := (@ThreeSum1960614.Machine.ThreeSum.LightSignedLeafGeneral.meets__implementation_4333f95165)

#print axioms solution
