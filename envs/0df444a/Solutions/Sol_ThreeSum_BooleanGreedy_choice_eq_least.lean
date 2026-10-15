-- Prove2me | solution 1 for ThreeSum.BooleanGreedy.choice_eq_least
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:10:08.784+00:00
-- url     : https://prove2.me/submissions/c842932a-cb95-45d0-bdaa-8e6a2d4c9e50

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
namespace Light
end Light
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
# A finite array minimum scan in the benchmark language

The selected index is a deterministic left-to-right minimum. Its value
can therefore instantiate the exact mean bound for offset balancing.
-/

namespace ThreeSum.LightMinimum

open Light





theorem least_lt (f : ℕ → ℤ) {n : ℕ} (hn : 0 < n) : least f n < n := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => simp [least]
      | succ n =>
          have h := ih (by omega)
          unfold least
          split <;> omega


































variable {lim : Limits} {P : Program} {d : ℕ}





































end ThreeSum.LightMinimum

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




























theorem selectMap_indices {U : Type*} [DecidableEq U]
    (covers : ℕ → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap (List.range n) covers targets =
      least (fun i => -((targets.filter (covers i)).card : ℤ)) n := by
  unfold Cover.selectMap
  rw [argmax_range _ hn]
  rfl











end ThreeSum.IndexedGreedy

end

section


/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy

open Finset
open scoped BigOperators


















theorem state_subset (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    state matrix rows cols t ⊆ range cols := Cover.greedyState_subset ..







theorem score_eq_card {matrix : ℕ → ℕ → ℕ} {rows cols row : ℕ}
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1)
    (hrow : row < rows) (t : ℕ) :
    LightCoverScores.score matrix (active matrix rows cols t) cols row =
      ((state matrix rows cols t).filter (covers matrix row)).card := by
  have hset : ((range cols).filter fun j => j ∈ state matrix rows cols t ∧ covers matrix row j) =
      (state matrix rows cols t).filter (covers matrix row) := by
    ext j
    simp only [mem_filter]
    constructor
    · rintro ⟨_,hmem,hcover⟩
      exact ⟨hmem,hcover⟩
    · rintro ⟨hmem,hcover⟩
      exact ⟨state_subset matrix rows cols t hmem,hmem,hcover⟩
  rw [← hset,Finset.card_filter]
  unfold LightCoverScores.score LightBooleanDot.dot
  apply sum_congr rfl
  intro j hj
  have hm := hmatrix row hrow j (mem_range.mp hj)
  by_cases ha : j ∈ state matrix rows cols t <;> by_cases hc : matrix row j = 1
  · simp [active,ha,covers,hc]
  · have hz : matrix row j = 0 := by omega
    simp [active,ha,covers,hc,hz]
  · simp [active,ha,covers,hc]
  · simp [active,ha,covers,hc]






theorem choice_eq_least_sourceProof {matrix : ℕ → ℕ → ℕ} {rows cols : ℕ}
    (hrows : 0 < rows)
    (hmatrix : ∀ i < rows, ∀ j < cols, matrix i j ≤ 1) (t : ℕ) :
    choice matrix rows cols t =
      LightMinimum.least (fun i => -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ)) rows := by
  have hf : ∀ i < rows,
      -(((state matrix rows cols t).filter (covers matrix i)).card : ℤ) =
      -(LightCoverScores.score matrix (active matrix rows cols t) cols i : ℤ) := by
    intro i hi
    rw [score_eq_card hmatrix hi t]
  rw [choice,IndexedGreedy.selectMap_indices _ _ hrows]
  have hcongr (f g : ℕ → ℤ) : ∀ n, (∀ i < n, f i = g i) →
      LightMinimum.least f n = LightMinimum.least g n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro he
      cases n with
      | zero => simp [LightMinimum.least]
      | succ n =>
        have hb := LightMinimum.least_lt g (by omega : 0 < n+1)
        have hi := ih (fun i hi => he i (by omega))
        change (if f (n+1) < f (LightMinimum.least f (n+1)) then n+1 else _) = _
        rw [hi,he (n+1) (by omega),he _ (by omega)]
        rfl
  exact hcongr _ _ rows hf




























end ThreeSum.BooleanGreedy

end


theorem solution : ∀ {matrix : Nat → Nat → Nat} {rows cols : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) rows →
    (∀ (i : Nat),
        @LT.lt.{0} Nat instLTNat i rows →
          ∀ (j : Nat),
            @LT.lt.{0} Nat instLTNat j cols →
              @LE.le.{0} Nat instLENat (matrix i j) (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) →
      ∀ (t : Nat),
        @Eq.{1} Nat (ThreeSum.BooleanGreedy.choice matrix rows cols t)
          (ThreeSum.LightMinimum.least
            (fun (i : Nat) =>
              @Neg.neg.{0} Int Int.instNegInt
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.LightCoverScores.score matrix (ThreeSum.BooleanGreedy.active matrix rows cols t) cols i)))
            rows) := by
  exact @ThreeSum.BooleanGreedy.choice_eq_least_sourceProof

#print axioms solution
