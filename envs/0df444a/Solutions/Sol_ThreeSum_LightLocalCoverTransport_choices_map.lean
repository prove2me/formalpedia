-- Prove2me | solution 1 for ThreeSum.LightLocalCoverTransport.choices_map
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:10:42.766909+00:00
-- url     : https://prove2.me/submissions/549aa4e0-7154-415c-a525-f34f71502f99

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Theorems.Thm_ThreeSum_IndexedGreedy_argmax_range


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LightMinimum
end ThreeSum.LightMinimum

section


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

















































theorem greedyState_spec (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) (u : U) :
    u ∈ greedyState maps covers targets t ↔
      u ∈ targets ∧ ∀ ω ∈ greedyChoices maps covers targets t, ¬ covers ω u := by
  induction t with
  | zero => simp [greedyState, greedyChoices]
  | succ t ih =>
    simp only [greedyState, mem_filter, greedyChoices, List.mem_append, List.mem_singleton, ih]
    aesop

theorem greedyState_subset (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) (t : ℕ) :
    greedyState maps covers targets t ⊆ targets := by
  intro u hu
  exact ((greedyState_spec maps covers targets t u).mp hu).1
























































































end ThreeSum.Cover

end

section


/-!
# Linking array extrema to the finite greedy-cover definition

The program scans indices in increasing order and retains the first
maximum. This is exactly the tie rule in `List.argmax` used by the
mathematical cover construction.
-/

namespace ThreeSum.IndexedGreedy

open LightMinimum
















theorem argmax_map {α β : Type*} (g : α → β) (f : β → ℕ) (xs : List α) :
    (xs.map g).argmax f = (xs.argmax (f ∘ g)).map g := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.map_append,List.map_singleton,List.argmax_concat,ih,List.argmax_concat]
    cases h : xs.argmax (f ∘ g) with
    | none => rfl
    | some y =>
      simp only [Option.map_some,Function.comp_apply]
      split <;> rfl




















end ThreeSum.IndexedGreedy

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators


















theorem state_subset (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    state matrix rows cols t ⊆ range cols := Cover.greedyState_subset ..





























































































end ThreeSum.BooleanGreedy

end

section


/-!
# Exact transport of the Boolean greedy schedule

Relabeling targets by a bijection preserves every score. Mapping the
candidate list in its existing order then preserves the first-maximum tie
rule and the complete choice list, including repeated occurrences.
-/

namespace ThreeSum.LightLocalCoverTransport

open Finset

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

theorem choices_map_sourceProof
    (matrix : ℕ → ℕ → ℕ) (candidate : ℕ → Ω) (target : ℕ → U)
    (covers : Ω → U → Prop) [DecidableRel covers]
    {rows cols : ℕ} (hrows : 0 < rows)
    (hinj : Set.InjOn target (range cols))
    (hcover : ∀ i, ∀ j < cols, BooleanGreedy.covers matrix i j ↔ covers (candidate i) (target j))
    (rounds : ℕ) :
    (BooleanGreedy.choices matrix rows cols rounds).map candidate =
      Cover.greedyChoices ((List.range rows).map candidate) covers
        ((range cols).image target) rounds := by
  have hscore (old : Finset ℕ) (hold : old ⊆ range cols) (i : ℕ) :
      ((old.image target).filter (covers (candidate i))).card =
        (old.filter (BooleanGreedy.covers matrix i)).card := by
    rw [filter_image]
    have hfilter : (old.filter fun j => covers (candidate i) (target j)) =
        old.filter (BooleanGreedy.covers matrix i) := by
      apply filter_congr
      intro j hj
      exact (hcover i j (mem_range.mp (hold hj))).symm
    rw [hfilter]
    apply card_image_of_injOn
    intro a ha b hb he
    exact hinj (hold (mem_filter.mp ha).1) (hold (mem_filter.mp hb).1) he
  have hselect (old : Finset ℕ) (hold : old ⊆ range cols) :
      Cover.selectMap ((List.range rows).map candidate) covers (old.image target) =
        candidate (Cover.selectMap (List.range rows) (BooleanGreedy.covers matrix) old) := by
    unfold Cover.selectMap
    rw [IndexedGreedy.argmax_map]
    have hf : (fun x => ((old.image target).filter (covers x)).card) ∘ candidate =
        (fun i => (old.filter (BooleanGreedy.covers matrix i)).card) := by
      funext i
      exact hscore old hold i
    rw [hf,IndexedGreedy.argmax_range _ hrows]
    rfl
  have hstates : ∀ t,
      (BooleanGreedy.state matrix rows cols t).image target =
        Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      change ((BooleanGreedy.state matrix rows cols t).filter
          (fun j => ¬BooleanGreedy.covers matrix (BooleanGreedy.choice matrix rows cols t) j)).image target =
        (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t).filter
          (fun u => ¬covers (Cover.selectMap ((List.range rows).map candidate) covers
            (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t)) u)
      rw [← ih,hselect _ (BooleanGreedy.state_subset matrix rows cols t),filter_image]
      apply congrArg (Finset.image target)
      apply filter_congr
      intro j hj
      exact not_congr (hcover _ j (mem_range.mp (BooleanGreedy.state_subset matrix rows cols t hj)))
  induction rounds with
  | zero => rfl
  | succ t ih =>
    change (BooleanGreedy.choices matrix rows cols t ++ [BooleanGreedy.choice matrix rows cols t]).map candidate =
      Cover.greedyChoices ((List.range rows).map candidate) covers ((range cols).image target) t ++
        [Cover.selectMap ((List.range rows).map candidate) covers
          (Cover.greedyState ((List.range rows).map candidate) covers ((range cols).image target) t)]
    rw [List.map_append,List.map_singleton,ih,← hstates t,
      hselect _ (BooleanGreedy.state_subset matrix rows cols t)]
    rfl

end ThreeSum.LightLocalCoverTransport

end

universe u_1 u_2

theorem solution : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [inst_1 : DecidableEq.{u_2 + 1} U]
  (matrix : Nat → Nat → Nat) (candidate : Nat → Ω) (target : Nat → U) (covers : Ω → U → Prop)
  [inst_2 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] {rows cols : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows →
    @Set.InjOn.{0, u_2} Nat U target
        (@SetLike.coe.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat) (Finset.range cols)) →
      (∀ (i j : Nat),
          @LT.lt.{0} Nat instLTNat j cols →
            Iff (ThreeSum.BooleanGreedy.covers matrix i j) (covers (candidate i) (target j))) →
        ∀ (rounds : Nat),
          @Eq.{u_1 + 1} (List.{u_1} Ω)
            (@List.map.{0, u_1} Nat Ω candidate (ThreeSum.BooleanGreedy.choices matrix rows cols rounds))
            (@ThreeSum.Cover.greedyChoices.{u_1, u_2} Ω U inst (@List.map.{0, u_1} Nat Ω candidate (List.range rows))
              covers inst_2 (@Finset.image.{0, u_2} Nat U inst_1 target (Finset.range cols)) rounds) := by
  exact @ThreeSum.LightLocalCoverTransport.choices_map_sourceProof

#print axioms solution
