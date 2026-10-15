-- Prove2me | solution 1 for ThreeSum.Cover.greedy_cover
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:11:38.208232+00:00
-- url     : https://prove2.me/submissions/a3bdad4c-3ff5-4274-bc94-989c8722d2a2

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
import Theorems.Thm_ThreeSum_Cover_greedyState_geometric


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

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












































/-- Each block of a iterations shrinks the geometric upper bound by 1/2. -/
theorem half_power_bound (a : ℕ) (ha : 0 < a) : 2 * (a - 1) ^ a ≤ a ^ a := by
  have hae : a - 1 + 1 = a := by omega
  have h := pow_add_mul_le_add_pow (a := a - 1) (b := 1)
    (Nat.zero_le _) (Nat.zero_le _) a
  simp only [hae, mul_one] at h
  have hpow : (a - 1) ^ a = (a - 1) ^ (a - 1) * (a - 1) := by
    calc
      (a - 1) ^ a = (a - 1) ^ ((a - 1) + 1) := congrArg ((a - 1) ^ ·) hae.symm
      _ = (a - 1) ^ (a - 1) * (a - 1) := pow_succ _ _
  have hm := Nat.mul_le_mul_left ((a - 1) ^ (a - 1)) (Nat.sub_le a 1)
  nlinarith

theorem greedyState_blocks [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 1 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) (k : ℕ) :
    2 ^ k * (greedyState maps covers targets (a * k)).card ≤ targets.card := by
  have ha0 : 0 < a := by omega
  have hgeom := greedyState_geometric maps hall covers targets a ha0 hfrequency (a * k)
  have hhalf := Nat.pow_le_pow_left (half_power_bound a ha0) k
  simp only [mul_pow, ← pow_mul] at hhalf
  have hpos : 0 < (a - 1) ^ (a * k) := Nat.pow_pos (by omega)
  have hm := Nat.mul_le_mul_right (greedyState maps covers targets (a * k)).card hhalf
  nlinarith

/-- The implemented greedy list covers every target within
a*(floor(log2(number of targets))+1) maps. -/
theorem greedy_cover_sourceProof [Fintype Ω] (maps : List Ω)
    (hall : ∀ ω, ω ∈ maps) (covers : Ω → U → Prop) [DecidableRel covers]
    (targets : Finset U) (a : ℕ) (ha : 1 < a)
    (hfrequency : ∀ u ∈ targets,
      Fintype.card Ω ≤ a * (univ.filter fun ω => covers ω u).card) :
    ∀ u ∈ targets,
      ∃ ω ∈ greedyChoices maps covers targets (a * (Nat.log2 targets.card + 1)),
        covers ω u := by
  have hblocks := greedyState_blocks maps hall covers targets a ha hfrequency
    (Nat.log2 targets.card + 1)
  have hlog := Nat.lt_log2_self (n := targets.card)
  have hzero : (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card = 0 := by
    by_contra hn
    have hp : 1 ≤ (greedyState maps covers targets (a * (Nat.log2 targets.card + 1))).card := by omega
    have hm := Nat.mul_le_mul_left (2 ^ (Nat.log2 targets.card + 1)) hp
    nlinarith
  intro u hu
  by_contra! hnone
  have hmem := (greedyState_spec maps covers targets _ u).mpr ⟨hu, hnone⟩
  simpa [card_eq_zero.mp hzero] using hmem

end ThreeSum.Cover

end

universe u_1 u_2

theorem solution : ∀ {Ω : Type u_1} {U : Type u_2} [inst : Inhabited.{u_1 + 1} Ω] [DecidableEq.{u_2 + 1} U] [inst_2 : Fintype.{u_1} Ω]
  (maps : List.{u_1} Ω),
  (∀ (ω : Ω), @Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω) maps ω) →
    ∀ (covers : Ω → U → Prop) [inst_3 : @DecidableRel.{u_1 + 1, u_2 + 1} Ω U covers] (targets : Finset.{u_2} U)
      (a : Nat),
      @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a →
        (∀ (u : U),
            @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
              @LE.le.{0} Nat instLENat (@Fintype.card.{u_1} Ω inst_2)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
                  (@Finset.card.{u_1} Ω {ω : Ω | covers ω u}))) →
          ∀ (u : U),
            @Membership.mem.{u_2, u_2} U (Finset.{u_2} U)
                (@SetLike.instMembership.{u_2, u_2} (Finset.{u_2} U) U (@Finset.instSetLike.{u_2} U)) targets u →
              ∃ (ω : Ω),
                And
                  (@Membership.mem.{u_1, u_1} Ω (List.{u_1} Ω) (@List.instMembership.{u_1} Ω)
                    (@ThreeSum.Cover.greedyChoices.{u_1, u_2} Ω U inst maps covers inst_3 targets
                      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
                        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                          (@Finset.card.{u_2} U targets).log2
                          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                    ω)
                  (covers ω u) := by
  exact @ThreeSum.Cover.greedy_cover_sourceProof

#print axioms solution
