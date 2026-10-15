-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:52:54.917209+00:00
-- url     : https://prove2.me/submissions/5428b639-5f80-43ba-ac93-cbdee6271f94

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
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
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetOffset_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetSetup_meets

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
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetOffset
end ThreeSum.LightSubsetOffset
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
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset
end ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset
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















































@[simp] theorem layerOffset_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L 0 = 0 := by
  simp [_root_.ThreeSum.SubsetAddress.layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _









































































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
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem cell_offset_lt {W i j : ℕ} (hi : i ≤ W) (hj : j ≤ W) :
    i*(W+1)+j < _root_.ThreeSum.LightPascal.tableSize W := by
  have hm := Nat.mul_le_mul_right (W+1) hi
  unfold _root_.ThreeSum.LightPascal.tableSize
  nlinarith











end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # The layer-offset scan for compact downset addresses -/

namespace ThreeSum.LightSubsetOffset
open _root_.ThreeSum.LightSubsetOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem layerOffset_bound (L k : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L k ≤ k*2^L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
    have hb := Nat.choose_le_two_pow L k
    nlinarith







end ThreeSum.LightSubsetOffset

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





theorem cap_eq {L cut : ℕ} (hcut : cut ≤ L) :
    _root_.ThreeSum.SubsetAddress.downsetCap L cut = _root_.ThreeSum.SubsetAddress.layerOffset L cut+L.choose cut := by
  simp only [_root_.ThreeSum.SubsetAddress.downsetCap,Nat.min_eq_left hcut,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]











end ThreeSum.LightDownsetSize

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightDownsetSize
open _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize

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

theorem ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets__implementation_abfef3a149 {pMain pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body pSetup pOffset))
    (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body)
    {μ : ℕ → ℤ} {L cut work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hd : d+L+4 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,work] μ (_root_.ThreeSum.LightDownsetSize.time L)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' work) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hpow : (2^L : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hsmall := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.layerOffset_bound L cut
  have hchoose := Nat.choose_le_two_pow L cut
  have hprod := Nat.mul_le_mul hcut hpow
  have hbound : _root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ (L+1)*2^(L+1) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.cap_eq hcut]
    nlinarith
  have hboundZ : (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbound : (downsetCap L cut : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hcast : (L : ℤ)*((L : ℤ)+1) = ((L*(L+1) : ℕ) : ℤ) := by push_cast; rfl
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.body _root_.ThreeSum.LightDownsetSize.time
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetSetup.meets (d := d+1) (μ := μ) (L := L) (k := 0) (m := 0)
    C hw hspace hword₀ (by simp) (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;> omega)
     on_goal -1 => (rintro _ μ₁ ⟨_, hTable, _, hKept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have ho := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets (d := d+1) hOffset μ₁ hw (by omega) hword hTable le_rfl hcut
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;> omega)
     on_goal -1 => (rintro off μ₂ ⟨hoff, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  have hread := hTable L le_rfl cut hcut
  have hcell := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.cell_offset_lt (show L ≤ L from le_rfl) hcut
  have haddr : ((work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ)).toNat = work+L*(L+1)+cut := by
    have hh : (work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ) = ((work+L*(L+1)+cut : ℕ) : ℤ) := by
      push_cast
      rfl
    rw [hh,Int.toNat_natCast]
  have hreadZ : μ₁ (((work : ℤ)+(L : ℤ)*((L : ℤ)+1)+(cut : ℤ)).toNat) = (L.choose cut : ℤ) := by
    rw [haddr,hread]
  have hsum : (_root_.ThreeSum.SubsetAddress.layerOffset L cut : ℤ)+(L.choose cut : ℤ) = (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℤ) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.cap_eq hcut,Nat.cast_add]
  have hn₁ : (0 : ℤ) ≤ _root_.ThreeSum.SubsetAddress.layerOffset L cut := Int.natCast_nonneg _
  have hn₂ : (0 : ℤ) ≤ L.choose cut := Int.natCast_nonneg _
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.downsetCap L cut : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hoff, hreadZ, hsum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hoff, hreadZ, hsum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hoff, hreadZ, hsum, _root_.ThreeSum.LightSubsetSetup.time, _root_.ThreeSum.LightSubsetOffset.time, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime, _root_.Light.powTableTime, _root_.ThreeSum.LightSubsetAddress.rankTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨by simp,hKept⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets__implementation_abfef3a149) := (@ThreeSum1960614.Machine.ThreeSum.LightDownsetSize.meets__implementation_abfef3a149)

#print axioms solution
