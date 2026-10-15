-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:28:01.839068+00:00
-- url     : https://prove2.me/submissions/817c35c3-51f9-4c0b-ac3c-4ed93359111f

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
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSourceGather_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightZetaStages_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightResidues
end ThreeSum.LightResidues
namespace ThreeSum.LightSourceRetainedStages
end ThreeSum.LightSourceRetainedStages
namespace ThreeSum.LightSourceStages
end ThreeSum.LightSourceStages
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.SourceTableLayout
end ThreeSum.SourceTableLayout
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightResidues
end ThreeSum1960614.Machine.ThreeSum.LightResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
end ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceStages
end ThreeSum1960614.Machine.ThreeSum.LightSourceStages
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.SourceTableLayout
end ThreeSum1960614.Machine.ThreeSum.SourceTableLayout
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









theorem enumerateThrough_length (L k : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateThrough L k).length = _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  | succ k ih =>
      rw [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.length_append, ih, _root_.ThreeSum.SubsetAddress.enumerateLayer_length,
        _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).length = _root_.ThreeSum.SubsetAddress.downsetCap L cut :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateThrough L k ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ k := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
  | succ k ih =>
      simp only [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.mem_append, ih, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateDownset L cut ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ cut := by
  rw [_root_.ThreeSum.SubsetAddress.enumerateDownset, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (_root_.ThreeSum.SubsetAddress.weight_le_width hm)⟩





































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

theorem residue_lt {p : ℕ} (hp : 0 < p) (c x : ℤ) : _root_.ThreeSum.LightResidues.residue p c x < p := by
  have h := Int.emod_lt_of_pos (c * x) (by exact_mod_cast hp : (0 : ℤ) < p)
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_cast hp] at h
  exact_mod_cast h















end ThreeSum.LightResidues

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout
open _root_.ThreeSum.SourceTableLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 800000

theorem layerRank_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerRank L 0 0 = 0 := by
  induction L with
  | zero => rfl
  | succ L ih => simpa only [_root_.ThreeSum.SubsetAddress.layerRank,if_pos (Nat.two_pow_pos L)] using ih

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β)
    (a : α) (b : β) {i : ℕ} (hi : i < l.length) :
    (l.map f).getD i b = f (l.getD i a) := by
  rw [List.getD_eq_getElem _ _ (by simpa using hi),List.getD_eq_getElem _ _ hi]
  exact List.getElem_map ..

theorem enumerateLayer_getD_rank {L k m : ℕ} (hm : _root_.ThreeSum.SubsetAddress.IsMask L k m) (fallback : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateLayer L k).getD (_root_.ThreeSum.SubsetAddress.layerRank L k m) fallback = m := by
  induction L generalizing k m fallback with
  | zero =>
      have hk := hm.le_width
      have hb := hm.1
      have hk0 : k=0 := by omega
      have hm0 : m=0 := by simp only [pow_zero] at hb; omega
      subst k; subst m
      simp [_root_.ThreeSum.SubsetAddress.enumerateLayer,_root_.ThreeSum.SubsetAddress.layerRank]
  | succ L ih =>
      cases k with
      | zero =>
          have hm0 := (_root_.ThreeSum.SubsetAddress.isMask_zero (L+1) m).mp hm
          subst m
          simp [_root_.ThreeSum.SubsetAddress.enumerateLayer,_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.layerRank_zero]
      | succ k =>
          rw [_root_.ThreeSum.SubsetAddress.enumerateLayer,if_pos hm.le_width]
          by_cases hc : m < 2^L
          · rw [_root_.ThreeSum.SubsetAddress.layerRank,if_pos hc]
            rw [List.getD_append _ _ _ _ (by
              rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]
              exact _root_.ThreeSum.SubsetAddress.layerRank_lt (hm.low hc))]
            exact ih (hm.low hc) fallback
          · have hh := (hm.high (Nat.le_of_not_gt hc)).2
            simp only [Nat.add_sub_cancel] at hh
            rw [_root_.ThreeSum.SubsetAddress.layerRank,if_neg hc]
            simp only [Nat.add_sub_cancel]
            rw [List.getD_append_right _ _ _ _ (by
              rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]
              omega),_root_.ThreeSum.SubsetAddress.enumerateLayer_length,Nat.add_sub_cancel_left]
            rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.getD_map_of_lt _ _ 0 _ (by
              rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]
              exact _root_.ThreeSum.SubsetAddress.layerRank_lt hh),ih hh 0]
            omega

theorem enumerateThrough_getD_rank {L k m cut : ℕ} (hm : _root_.ThreeSum.SubsetAddress.IsMask L k m)
    (hk : k ≤ cut) (fallback : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateThrough L cut).getD (_root_.ThreeSum.SubsetAddress.downsetRank L m) fallback = m := by
  induction cut with
  | zero =>
      have hk0 : k=0 := by omega
      subst k
      simpa only [_root_.ThreeSum.SubsetAddress.enumerateThrough,_root_.ThreeSum.SubsetAddress.downsetRank,hm.2,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_zero,zero_add] using
        _root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.enumerateLayer_getD_rank hm fallback
  | succ cut ih =>
      rw [_root_.ThreeSum.SubsetAddress.enumerateThrough]
      by_cases hlow : k ≤ cut
      · rw [List.getD_append _ _ _ _ (by
          rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length]
          have hlt := _root_.ThreeSum.SubsetAddress.layerRank_lt hm
          have hle := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ hlow)
          simp only [Nat.succ_eq_add_one] at hle
          rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L k] at hle
          unfold _root_.ThreeSum.SubsetAddress.downsetRank
          rw [hm.2]
          omega)]
        exact ih hlow
      · have he : k=cut+1 := by omega
        subst k
        rw [_root_.ThreeSum.SubsetAddress.downsetRank,hm.2]
        rw [List.getD_append_right _ _ _ _ (by
          rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length]
          omega),_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length,Nat.add_sub_cancel_left]
        exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.enumerateLayer_getD_rank hm fallback

theorem enumerateDownset_getD_rank {L cut m : ℕ}
    (hm : m < 2^L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) (fallback : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).getD (_root_.ThreeSum.SubsetAddress.downsetRank L m) fallback = m := by
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.enumerateThrough_getD_rank ⟨hm,rfl⟩ (le_min hk (_root_.ThreeSum.SubsetAddress.weight_le_width hm)) fallback

theorem enumerateDownset_getD_subsetRank {L cut : ℕ} (S : Finset (Fin L))
    (hS : S.card ≤ cut) (fallback : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).getD (_root_.ThreeSum.SubsetAddress.subsetRank S) fallback = _root_.ThreeSum.SubsetAddress.subsetMask S := by
  have hmask := _root_.ThreeSum.SubsetAddress.subsetMask_isMask S
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.enumerateDownset_getD_rank hmask.1 (hmask.2.trans_le hS) fallback





theorem maskAt_mem {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    _root_.ThreeSum.SourceTableLayout.maskAt L cut i ∈ _root_.ThreeSum.SubsetAddress.enumerateDownset L cut := by
  unfold _root_.ThreeSum.SourceTableLayout.maskAt
  rw [List.getD_eq_getElem _ _ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_length] using hi)]
  exact List.getElem_mem _

theorem maskAt_lt {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    _root_.ThreeSum.SourceTableLayout.maskAt L cut i < 2^L :=
  ((_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateDownset L cut _).mp (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.maskAt_mem hi)).1

theorem setAt_card {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    (_root_.ThreeSum.SourceTableLayout.setAt L cut i).card ≤ cut := by
  rw [_root_.ThreeSum.SourceTableLayout.setAt,_root_.ThreeSum.MaskDecode.decode_card (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.maskAt_lt hi)]
  exact ((_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateDownset L cut _).mp (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.maskAt_mem hi)).2



theorem setAt_subsetRank {L cut : ℕ} (S : Finset (Fin L)) (hS : S.card ≤ cut) :
    _root_.ThreeSum.SourceTableLayout.setAt L cut (_root_.ThreeSum.SubsetAddress.subsetRank S) = S := by
  rw [_root_.ThreeSum.SourceTableLayout.setAt,_root_.ThreeSum.SourceTableLayout.maskAt,_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.enumerateDownset_getD_subsetRank S hS,_root_.ThreeSum.MaskDecode.decode_subsetMask]



theorem tableAt_of_setAt {L cut base : ℕ} {μ : ℕ → ℤ}
    (f : Finset (Fin L) → ℤ)
    (hread : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap L cut, μ (base+i) = f (_root_.ThreeSum.SourceTableLayout.setAt L cut i)) :
    _root_.ThreeSum.LightZetaCell.TableAt μ base cut f := by
  intro S hS
  rw [hread _ (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS),_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.setAt_subsetRank S hS]

end ThreeSum.SourceTableLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histogram construction followed by all suffix zeta stages

This fixed program constructs a trimmed source table from the physical input
array, then feeds that exact table into the existing costed suffix transform.
The rank/enumeration proof connects the sequential source writes to the
compact addresses. No initially populated source or zeta table is assumed.
-/

namespace ThreeSum.LightSourceStages
open _root_.ThreeSum.LightSourceStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem ZetaProcs.meets {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceStages.ZetaProcs P pMain)
    {μ : ℕ → ℤ} {L cut base maskBase work U : ℕ} (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : _root_.ThreeSum.LightZetaCell.TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [L,cut,base,maskBase,work] μ (_root_.ThreeSum.LightZetaStages.time L cut)
      (fun _ ν => _root_.ThreeSum.LightZetaStages.StoredThrough ν base cut f L ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν maskBase base ((L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut)) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages.meets C.main C.size C.pass C.enumSetup C.enumeration C.batch C.cell
    C.setup C.offset C.erase f hw hcut hdata hmasks hspace hword hvalueWord hread hvalues hd























end ThreeSum.LightSourceStages

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Source stages gathered from a retained original-input histogram

The histogram is built once for a source band and fixed modulus/offset by
`LightSourceHistogram`. This program then gathers the independently trimmed
source for each occurrence vector and runs the actual suffix transforms.
Neither the original array nor the full histogram is rescanned in this loop.
-/

namespace ThreeSum.LightSourceRetainedStages
open _root_.ThreeSum.LightSourceRetainedStages


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000



theorem source_abs_le {L m B : ℕ} (hm : 0 < m)
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (S : Finset (Fin L)) :
    |_root_.ThreeSum.LightSourceRetainedStages.source m endpoint flag hist S| ≤ (B : ℤ) := by
  unfold _root_.ThreeSum.LightSourceRetainedStages.source
  rw [Int.abs_natCast]
  apply Int.ofNat_le.mpr
  split
  · exact hhist _ (_root_.ThreeSum1960614.Machine.ThreeSum.LightResidues.residue_lt hm 1 _)
  · omega











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}











end ThreeSum.LightSourceRetainedStages

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSourceRetainedStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
set_option maxHeartbeats 1800000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets__implementation_9ef1eb2459 {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {raw flags table base m work L cut maskBase E B : ℕ}
    (endpoint : Finset (Fin L) → ℤ) (flag : Finset (Fin L) → ℕ) (hist : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+8 ≤ lim.depth)
    (hm : 0 < m) (hcut : cut ≤ L)
    (hraw : raw+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ base) (hflags : flags+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ base)
    (htable : table+m ≤ base) (hdata : base+(L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ work)
    (hspace : _root_.ThreeSum.LightSourceRetainedStages.space work L E ≤ lim.space)
    (hword : (_root_.ThreeSum.LightSourceRetainedStages.word L m E B : ℤ) ≤ lim.word)
    (hrawRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap L cut,
      μ (raw+i) = endpoint (_root_.ThreeSum.SourceTableLayout.setAt L cut i))
    (hrawBound : ∀ S, S.card ≤ cut → |endpoint S| ≤ (E : ℤ))
    (hflagRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap L cut,
      μ (flags+i) = (flag (_root_.ThreeSum.SourceTableLayout.setAt L cut i) : ℤ))
    (hflagBound : ∀ S, S.card ≤ cut → flag S ≤ 1)
    (hhistRead : ∀ r < m, μ (table+r) = (hist r : ℤ))
    (hhistBound : ∀ r < m, hist r ≤ B) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [raw,flags,table,base,m,work,L,cut,maskBase,_root_.ThreeSum.SubsetAddress.downsetCap L cut]
      μ (_root_.ThreeSum.LightSourceRetainedStages.time L cut E) (fun _ ν =>
        _root_.ThreeSum.LightZetaStages.StoredThrough ν base cut (_root_.ThreeSum.LightSourceRetainedStages.source m endpoint flag hist) L ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by
  have hsGather : work+(Nat.log 2 (E+1)+2) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsZeta : work+_root_.ThreeSum.LightPascal.tableSize L+(L+1) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwGather : (4*E+4*m+16 : ℤ) ≤ lim.word := by
    have hh : 4*E+4*m+16 ≤ _root_.ThreeSum.LightSourceRetainedStages.word L m E B := by unfold _root_.ThreeSum.LightSourceRetainedStages.word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hwB : (B : ℤ) ≤ lim.word := by
    have hh : B ≤ _root_.ThreeSum.LightSourceRetainedStages.word L m E B := by unfold _root_.ThreeSum.LightSourceRetainedStages.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwZeta : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (L+1)*2^(L+1) ≤ _root_.ThreeSum.LightSourceRetainedStages.word L m E B := by unfold _root_.ThreeSum.LightSourceRetainedStages.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwValues : ((2^L*B : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^L*B ≤ _root_.ThreeSum.LightSourceRetainedStages.word L m E B := by unfold _root_.ThreeSum.LightSourceRetainedStages.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hcap : _root_.ThreeSum.SubsetAddress.downsetCap L cut ≤ (L+1)*_root_.ThreeSum.SubsetAddress.downsetCap L cut :=
    Nat.le_mul_of_pos_left _ (by omega)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.body _root_.ThreeSum.LightSourceRetainedStages.time
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceGather.meets C.gather C.emod (d := d+1) (μ := μ)
    (raw := raw) (flags := flags) (table := table) (dst := base)
    (n := _root_.ThreeSum.SubsetAddress.downsetCap L cut) (m := m) (work := work) (U := E) (B := B)
    (fun i => endpoint (_root_.ThreeSum.SourceTableLayout.setAt L cut i))
    (fun i => flag (_root_.ThreeSum.SourceTableLayout.setAt L cut i)) hist
    hw (by omega) hm hraw hflags htable (by omega) hsGather hwGather hwB
    hrawRead (fun i hi => hrawBound _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.setAt_card hi))
    hflagRead (fun i hi => hflagBound _ (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.setAt_card hi)) hhistRead hhistBound
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time] <;> omega)
     on_goal -1 => (rintro r ν₁ ⟨out, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have htableAt : _root_.ThreeSum.LightZetaCell.TableAt ν₁ base cut (_root_.ThreeSum.LightSourceRetainedStages.source m endpoint flag hist) := by
    apply _root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.tableAt_of_setAt
    exact out
  have hz := C.zeta.meets (d := d+1) (μ := ν₁) (L := L) (cut := cut)
    (base := base) (maskBase := maskBase) (work := work) (U := B)
    (_root_.ThreeSum.LightSourceRetainedStages.source m endpoint flag hist) hw hcut hdata hmasks hsZeta hwZeta hwValues htableAt
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.source_abs_le hm endpoint flag hist hhistBound S) (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hz _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hz ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSourceGather.time, _root_.ThreeSum.LightZetaStages.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨stored, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨stored,?_⟩
  intro a ha
  exact (kept₂ a ⟨by omega,Or.inl (by omega)⟩).trans
    (kept₁ a ⟨by omega,Or.inl ha⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets__implementation_9ef1eb2459) := (@ThreeSum1960614.Machine.ThreeSum.LightSourceRetainedStages.Procs.meets__implementation_9ef1eb2459)

#print axioms solution
