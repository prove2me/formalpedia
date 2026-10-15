-- Prove2me | solution 1 for ThreeSum.Cover.greedyState_geometric
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:42:33.301693+00:00
-- url     : https://prove2.me/submissions/558fd9b1-50a8-44c4-af74-caa5da055f4d

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.MinMax
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

section


/-!
# Finite cover bounds

Finite, exact lemmas for the second-moment argument, deterministic averaging,
and composition used in the proposed construction.  A hypothesis about a
particular local hash family is a mathematical obligation, not an asserted
implementation or running-time theorem.
-/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators






























































/-- Exact double counting of the incidence relation. -/
theorem incidence_card_sum {Ω U : Type*} [Fintype Ω] [DecidableEq U]
    (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] :
    (∑ ω, (targets.filter (covers ω)).card) =
      ∑ u ∈ targets, (univ.filter fun ω => covers ω u).card := by
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

/-- A finite positive average produces a deterministic good choice. -/
theorem exists_good_cover {Ω U : Type*} [Fintype Ω] [Nonempty Ω]
    [DecidableEq U] (targets : Finset U) (covers : Ω → U → Prop)
    [DecidableRel covers] (a : ℕ)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∃ ω, targets.card ≤ a * (targets.filter (covers ω)).card := by
  by_contra! hnone
  have hlow := sum_le_sum hfrequency
  have hhigh : (∑ ω, a * (targets.filter (covers ω)).card) <
      ∑ _ω : Ω, targets.card := by
    exact sum_lt_sum_of_nonempty (by simp) (by simpa using hnone)
  simp only [sum_const, nsmul_eq_mul, card_univ, ← mul_sum] at hlow hhigh
  rw [incidence_card_sum targets covers] at hhigh
  nlinarith

/-- An exact survivor recurrence after choosing a good map. -/
theorem survivor_step {U : Type*} [DecidableEq U]
    (targets : Finset U) (covers : U → Prop) [DecidablePred covers]
    (a : ℕ) (ha : 0 < a)
    (hgood : targets.card ≤ a * (targets.filter covers).card) :
    a * (targets.filter fun u => ¬ covers u).card ≤ (a - 1) * targets.card := by
  have hc := card_filter_add_card_filter_not (s := targets) (p := covers)
  have ha' : a - 1 + 1 = a := by omega
  nlinarith

end ThreeSum.Cover

end

section


/-! # An executable finite greedy cover and its logarithmic length bound -/

namespace ThreeSum.Cover

open Finset
open scoped BigOperators

variable {Ω U : Type*} [Inhabited Ω] [DecidableEq U]

















theorem selectMap_max (maps : List Ω) (covers : Ω → U → Prop)
    [DecidableRel covers] (targets : Finset U) {ω : Ω} (hω : ω ∈ maps) :
    (targets.filter (covers ω)).card ≤
      (targets.filter (covers (selectMap maps covers targets))).card := by
  unfold selectMap
  cases h : maps.argmax (fun ω => (targets.filter (covers ω)).card) with
  | none => have := List.argmax_eq_none.mp h; simp_all
  | some v =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmax (f := fun ω => (targets.filter (covers ω)).card)
      hω (by simpa only [Option.mem_def] using h)





















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

theorem greedyState_contract [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a * (greedyState maps covers targets (t + 1)).card ≤
      (a - 1) * (greedyState maps covers targets t).card := by
  let old := greedyState maps covers targets t
  have hfreq : ∀ u ∈ old,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card := by
    intro u hu
    exact hfrequency u (greedyState_subset maps covers targets t hu)
  obtain ⟨ω, hω⟩ := exists_good_cover old covers a hfreq
  have hbest := selectMap_max maps covers old (hall ω)
  exact survivor_step old (covers (selectMap maps covers old)) a ha
    (hω.trans (Nat.mul_le_mul_left a hbest))

/-- The exact geometric recurrence, with all denominators cleared. -/
theorem greedyState_geometric_sourceProof [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 0 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (t : ℕ) :
    a ^ t * (greedyState maps covers targets t).card ≤ (a - 1) ^ t * targets.card := by
  induction t with
  | zero => simp [greedyState]
  | succ t ih =>
    have hs := greedyState_contract maps hall covers targets a ha hfrequency t
    calc
      a ^ (t + 1) * (greedyState maps covers targets (t + 1)).card =
          a ^ t * (a * (greedyState maps covers targets (t + 1)).card) := by ring
      _ ≤ a ^ t * ((a - 1) * (greedyState maps covers targets t).card) :=
        Nat.mul_le_mul_left _ hs
      _ = (a - 1) * (a ^ t * (greedyState maps covers targets t).card) := by ring
      _ ≤ (a - 1) * ((a - 1) ^ t * targets.card) := Nat.mul_le_mul_left _ ih
      _ = (a - 1) ^ (t + 1) * targets.card := by ring



















































end ThreeSum.Cover

end

universe u_1 u_2

theorem solution : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [DecidableEq.{u_2 + 1} U] [inst_2 : Fintype.{u_1} Ω]
  (maps : List.{u_1} Ω),
  (∀ (ω : Ω), @Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω) maps ω) →
    ∀ (covers : Ω → U → Prop) [inst_3 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] (targets : Finset.{u_2} U)
      (a : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) a →
        (∀ (u : U),
            @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
              @LE.le.{0} Nat instLENat (@Fintype.card.{u_1} Ω inst_2)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
                  (@Finset.card.{u_1} Ω {ω : Ω | covers ω u}))) →
          ∀ (t : Nat),
            @LE.le.{0} Nat instLENat
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) a t)
                (@Finset.card.{u_2} U (@ThreeSum.Cover.greedyState.{u_1, u_2} Ω U inst maps covers inst_3 targets t)))
              (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                  (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
                  (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) a
                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  t)
                (@Finset.card.{u_2} U targets)) := by
  exact @ThreeSum.Cover.greedyState_geometric_sourceProof

#print axioms solution
