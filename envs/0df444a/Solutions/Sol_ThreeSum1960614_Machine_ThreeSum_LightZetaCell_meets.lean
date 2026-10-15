-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightZetaCell.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:56:16.896353+00:00
-- url     : https://prove2.me/submissions/37725f6e-98ad-4dc0-8540-41ba5f4ac1c6

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightMaskErase_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetAddress_rank_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetOffset_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetSetup_meets
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_le
import Theorems.Thm_ThreeSum_MaskErase_eraseMask_maskOf
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

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
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
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
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
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









/-! ## The rules -/





























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase
open _root_.ThreeSum.MaskErase


open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress









theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.SubsetAddress.natPositions (s.erase a) = (_root_.ThreeSum.SubsetAddress.natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) = _root_.ThreeSum.SubsetAddress.subsetMask (s.erase a) := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.MaskErase.eraseMask_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s),
    ← _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.natPositions_erase, ← _root_.ThreeSum.SubsetAddress.subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) ≠ _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, (_root_.ThreeSum.SubsetAddress.subsetMask_injective L).ne_iff, Finset.erase_ne_self]

theorem eraseMask_lt_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    _root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s) < _root_.ThreeSum.SubsetAddress.subsetMask s ↔ a ∈ s := by
  have hb := _root_.ThreeSum.MaskErase.eraseMask_le (a := a.val) (_root_.ThreeSum.SubsetAddress.subsetMask_isMask s).1
  rw [lt_iff_le_and_ne]
  simpa only [hb, true_and] using _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_ne_iff s a

theorem eraseMask_isMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) (ha : a ∈ s) :
    _root_.ThreeSum.SubsetAddress.IsMask L (s.card-1) (_root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask s)) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
  exact _root_.ThreeSum.SubsetAddress.subsetMask_isMask (s.erase a)

end ThreeSum.MaskErase

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
# An actual compact-table zeta-cell update

The fixed procedure builds its own Pascal and power tables, ranks the input
mask, deletes the requested coordinate, ranks the smaller mask if necessary,
and writes the zeta addition at the compact downset address. The scratch area
is polynomial in the width. Neither addresses nor table values are supplied
by an oracle.
-/

namespace ThreeSum.LightZetaCell
open _root_.ThreeSum.LightZetaCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}









section

private theorem private_f7f1c26608_rank_offset {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.layerRank L S.card (_root_.ThreeSum.SubsetAddress.subsetMask S) + _root_.ThreeSum.SubsetAddress.layerOffset L S.card = _root_.ThreeSum.SubsetAddress.subsetRank S := by
  simp only [_root_.ThreeSum.SubsetAddress.subsetRank, _root_.ThreeSum.SubsetAddress.downsetRank, (_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).2, Nat.add_comm]
end












end ThreeSum.LightZetaCell

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightZetaCell.meets__implementation_0654541ac7 {pThis pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hThis : P[pThis]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body pSetup pOffset pErase pRank))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    (hErase : P[pErase]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst work U d : ℕ}
    (S : Finset (Fin L)) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work) (hdst : dst+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hS : S.card ≤ cut) (hd : d+L+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pThis d [L,S.card,_root_.ThreeSum.SubsetAddress.subsetMask S,a.val,src,dst,work] μ (_root_.ThreeSum.LightZetaCell.time L)
      (fun _ μ' => μ' (dst+_root_.ThreeSum.SubsetAddress.subsetRank S) = _root_.ThreeSum.Subset.zetaStep a f S ∧
        _root_.ThreeSum.LightZetaCell.KeptExcept μ μ' work (dst+_root_.ThreeSum.SubsetAddress.subsetRank S)) := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask S
  have hk := hm.le_width
  have hrS := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hfS := abs_le.mp (hvalues S hS)
  have hRankSum : (_root_.ThreeSum.SubsetAddress.layerRank L S.card (_root_.ThreeSum.SubsetAddress.subsetMask S) : ℤ) +
      (_root_.ThreeSum.SubsetAddress.layerOffset L S.card : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetRank S : ℤ) := by
    exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.private_f7f1c26608_rank_offset S
  have hRankNonneg : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.layerRank L S.card (_root_.ThreeSum.SubsetAddress.subsetMask S) := Int.natCast_nonneg _
  have hOffsetNonneg : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.layerOffset L S.card := Int.natCast_nonneg _
  have hcastSize : ((L : ℤ)+1)*((L : ℤ)+1) = (_root_.ThreeSum.LightPascal.tableSize L : ℤ) := by
    simp [_root_.ThreeSum.LightPascal.tableSize,pow_two]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hThis
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.body _root_.ThreeSum.LightZetaCell.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (work + _root_.ThreeSum.LightPascal.tableSize L : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcastSize]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hcastSize] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcastSize] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hSetup := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.meets (d := d+1) (μ := μ) C hw hspace hword₀ hm (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hSetup _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hSetup ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro fullRank μ₁ ⟨hFullRank, hTable, hPowers, hKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hSread : μ₁ (src+_root_.ThreeSum.SubsetAddress.subsetRank S) = f S :=
    (hKept _ (by omega)).trans (hread S hS)
  have hOff := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega) hword hTable le_rfl hk
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hOff _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hOff ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro fullOffset μ₂ ⟨hFullOffset, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetRank S : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hFullRank, hFullOffset, hRankSum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hFullRank, hFullOffset, hRankSum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hFullRank, hFullOffset, hRankSum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hDel := _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskErase.meets hErase μ₁ hw hspace hword₀ hPowers
    L a.val (_root_.ThreeSum.SubsetAddress.subsetMask S) le_rfl (Nat.le_of_lt a.isLt) hm.1 (d+1) (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hDel _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hDel ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
     on_goal -1 => (rintro erased μ₂ ⟨hErased, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((_root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask S) : ℤ) < (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ)) (fun hbitZ => ?_) (fun hnotZ => ?_) ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErased, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hErased, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErased, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
     all_goals
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
  · have ha : a ∈ S := (_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_lt_iff S a).mp (by exact_mod_cast hbitZ)
    have hkpos : 0 < S.card := Finset.card_pos.mpr ⟨a,ha⟩
    have hsubCard : (S.card : ℤ)-1 = ((S.card-1 : ℕ) : ℤ) := by omega
    have hE : (S.erase a).card ≤ cut := (Finset.card_le_card (Finset.erase_subset _ _)).trans hS
    have hrE := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hE
    have hfE := abs_le.mp (hvalues (S.erase a) hE)
    have hEread : μ₁ (src+_root_.ThreeSum.SubsetAddress.subsetRank (S.erase a)) = f (S.erase a) :=
      (hKept _ (by omega)).trans (hread _ hE)
    have hMask := _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_isMask S a ha
    have hkE : S.card-1 ≤ L := by omega
    have hRankE : (_root_.ThreeSum.SubsetAddress.layerRank L (S.card-1) (_root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask S)) : ℤ) +
        (_root_.ThreeSum.SubsetAddress.layerOffset L (S.card-1) : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetRank (S.erase a) : ℤ) := by
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell.private_f7f1c26608_rank_offset (S.erase a)
    have hRankENonneg : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.layerRank L (S.card-1) (_root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask S)) :=
      Int.natCast_nonneg _
    have hOffsetENonneg : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.layerOffset L (S.card-1) := Int.natCast_nonneg _
    have hRankCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.rank_meets C.rank μ₁ hw (by omega) hspace hword₀ hTable hPowers
      L (S.card-1) (_root_.ThreeSum.MaskErase.eraseMask L a.val (_root_.ThreeSum.SubsetAddress.subsetMask S)) le_rfl hMask (d+1) (by omega)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hRankCall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hRankCall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErased, hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hErased, hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErased, hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
       on_goal -1 => (rintro erasedRank μ₂ ⟨hErasedRank, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₂
    have hOffCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega)
      hword hTable le_rfl hkE
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hOffCall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hOffCall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsubCard, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
       on_goal -1 => (rintro erasedOffset μ₂ ⟨hErasedOffset, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₂
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetRank (S.erase a) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hErasedRank, hErasedOffset, hRankE, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hErasedRank, hErasedOffset, hRankE, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hErasedRank, hErasedOffset, hRankE, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + _root_.ThreeSum.SubsetAddress.subsetRank S) (f S + f (S.erase a)) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSread, hEread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hSread, hEread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSread, hEread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    constructor
    · simp only [Function.update_self, _root_.ThreeSum.Subset.zetaStep, ha, ite_true]
    · intro i hi hne
      change Function.update μ₁ (dst+_root_.ThreeSum.SubsetAddress.subsetRank S) (f S + f (S.erase a)) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
  · have ha : a ∉ S := by
      intro ha
      exact hnotZ (by exact_mod_cast (_root_.ThreeSum1960614.Machine.ThreeSum.MaskErase.eraseMask_lt_iff S a).mpr ha)
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + _root_.ThreeSum.SubsetAddress.subsetRank S) (f S) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hSread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hSread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hSread, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightMaskErase.time, _root_.ThreeSum.LightSubsetAddress.rankTime, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    constructor
    · simp only [Function.update_self, _root_.ThreeSum.Subset.zetaStep, ha, ite_false]
    · intro i hi hne
      change Function.update μ₁ (dst+_root_.ThreeSum.SubsetAddress.subsetRank S) (f S) i = μ i
      rw [Function.update_of_ne hne]
      exact hKept i hi
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightZetaCell.meets__implementation_0654541ac7) := (@ThreeSum1960614.Machine.ThreeSum.LightZetaCell.meets__implementation_0654541ac7)

#print axioms solution
