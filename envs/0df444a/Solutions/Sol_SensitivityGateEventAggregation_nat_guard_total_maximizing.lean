-- Prove2me | solution 1 for SensitivityGateEventAggregation.nat_guard_total_maximizing
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:19:47.944273+00:00
-- url     : https://prove2.me/submissions/c77072e8-d28e-4629-ac3f-368dc8b8cdc0

import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GateEventAggregation
import Definitions.Def_Sensitivity214439_PairedSemantic_Solutions_GuardFeeAggregation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityFiniteRanks
end SensitivityFiniteRanks
namespace SensitivityGateEventAggregation
end SensitivityGateEventAggregation
namespace SensitivityGuardEvents
end SensitivityGuardEvents
namespace SensitivityGuardFeeAggregation
end SensitivityGuardFeeAggregation
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityLocalNumericSemantics
end SensitivityLocalNumericSemantics
namespace SensitivityPairedGuardNumericSlices
end SensitivityPairedGuardNumericSlices
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction
namespace SensitivitySocketEventSupport
end SensitivitySocketEventSupport

section


/-! Exact aggregation of occupied and unoccupied physical guard costs. -/
namespace SensitivityGuardFeeAggregation

noncomputable section
open scoped Classical BigOperators
set_option autoImplicit false









theorem maximizingSlots_range (baseline upward : ℝ) :
    1 ≤ maximizingSlots baseline upward ∧ maximizingSlots baseline upward ≤ 2 := by
  unfold maximizingSlots
  split_ifs <;> omega

theorem maximizingSlots_sound (baseline upward : ℝ) (slots : ℕ)
    (hslots : 1 ≤ slots ∧ slots ≤ 2) :
    ((slots - 1 : ℕ) : ℝ) * upward - slots * baseline ≤
      ((maximizingSlots baseline upward - 1 : ℕ) : ℝ) * upward -
        maximizingSlots baseline upward * baseline := by
  have hs : slots = 1 ∨ slots = 2 := by omega
  rcases hs with rfl | rfl <;>
    unfold maximizingSlots <;> split_ifs <;> norm_num <;> linarith

theorem guard_total_normal_form {G : Type} (occupied : Finset G) (slots : G → ℕ)
    (D : ℕ) (hslots : (∑ check ∈ occupied, slots check) ≤ D)
    (combined upward : G → ℝ) (baseline : ℝ) :
    ((D - ∑ check ∈ occupied, slots check : ℕ) : ℝ) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check - 1 : ℕ) * upward check) =
      D * baseline + ∑ check ∈ occupied,
        (combined check + (slots check - 1 : ℕ) * upward check - slots check * baseline) := by
  rw [Nat.cast_sub hslots,Nat.cast_sum,Finset.sum_sub_distrib,← Finset.sum_mul]
  ring

/-- Replacing each actual one/two-socket occupied guard by the maximizing
choice used in the numeric evaluator can only increase the total fee. The
natural subtraction stays exact because both total slot counts are ≤D. -/
theorem aggregate_maximizing_slots {G : Type} (occupied : Finset G) (slots : G → ℕ)
    (D : ℕ) (combined upward : G → ℝ) (baseline : ℝ)
    (hrange : ∀ check ∈ occupied, 1 ≤ slots check ∧ slots check ≤ 2)
    (hactual : (∑ check ∈ occupied, slots check) ≤ D)
    (hchosen : (∑ check ∈ occupied, maximizingSlots baseline (upward check)) ≤ D) :
    ((D - ∑ check ∈ occupied, slots check : ℕ) : ℝ) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check - 1 : ℕ) * upward check) ≤
      ((D - ∑ check ∈ occupied, maximizingSlots baseline (upward check) : ℕ) : ℝ) * baseline +
        ∑ check ∈ occupied, (combined check +
          (maximizingSlots baseline (upward check) - 1 : ℕ) * upward check) := by
  rw [guard_total_normal_form occupied slots D hactual,
    guard_total_normal_form occupied (fun check => maximizingSlots baseline (upward check)) D hchosen]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro check hc
  have h := maximizingSlots_sound baseline (upward check) (slots check) (hrange check hc)
  linarith





end
end SensitivityGuardFeeAggregation

end

section


/-! Summing exact own-socket and guard slices, with physical guard slots. -/
namespace SensitivityGateEventAggregation

noncomputable section
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityFiniteRanks SensitivityGuardEvents SensitivitySocketEventSupport
open SensitivityLocalNumericSemantics SensitivityPairedGuardNumericSlices
open SensitivityGuardFeeAggregation
set_option autoImplicit false

















theorem scaled_guard_total {G : Type} (occupied : Finset G) (slots : G → ℕ)
    (D : ℕ) (combined upward : G → ℕ) (baseline : ℕ) (scale : ℝ) :
    ((D - ∑ check ∈ occupied, slots check : ℕ) : ℝ) * (scale * (baseline : ℕ)) +
      ∑ check ∈ occupied, (scale * (combined check : ℕ) +
        (slots check - 1 : ℕ) * (scale * (upward check : ℕ))) =
      scale * ((D - ∑ check ∈ occupied, slots check) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check - 1) * upward check) : ℕ) := by
  push_cast
  rw [mul_add,Finset.mul_sum]
  have hsum : (∑ check ∈ occupied, (scale * (combined check : ℝ) +
      (slots check-1 : ℕ)*(scale*(upward check : ℝ)))) =
      ∑ check ∈ occupied, scale * ((combined check : ℝ) + (slots check-1 : ℕ)*(upward check : ℝ)) := by
    apply Finset.sum_congr rfl
    intro check _
    ring
  rw [hsum]
  ring



theorem maximizingNatSlots_eq (baseline upward : ℕ) :
    maximizingNatSlots baseline upward = maximizingSlots (baseline : ℝ) (upward : ℝ) := by
  simp only [maximizingNatSlots,maximizingSlots,Nat.cast_lt]







end
end SensitivityGateEventAggregation

end

/-! Summing exact own-socket and guard slices, with physical guard slots. -/
open SensitivityGateEventAggregation
open scoped Classical BigOperators
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
open SensitivityFiniteRanks SensitivityGuardEvents SensitivitySocketEventSupport
open SensitivityLocalNumericSemantics SensitivityPairedGuardNumericSlices
open SensitivityGuardFeeAggregation
set_option autoImplicit false

theorem solution {G : Type} (occupied : Finset G) (slots : G → ℕ)
    (D : ℕ) (combined upward : G → ℕ) (baseline : ℕ)
    (hrange : ∀ check ∈ occupied, 1 ≤ slots check ∧ slots check ≤ 2)
    (hactual : (∑ check ∈ occupied, slots check) ≤ D)
    (hroom : occupied.card * 2 ≤ D) :
    (((D - ∑ check ∈ occupied, slots check) * baseline +
        ∑ check ∈ occupied, (combined check + (slots check-1) * upward check) : ℕ) : ℝ) ≤
      (((D - ∑ check ∈ occupied, maximizingNatSlots baseline (upward check)) * baseline +
        ∑ check ∈ occupied, (combined check +
          (maximizingNatSlots baseline (upward check)-1)*upward check) : ℕ) : ℝ) := by
  have hchosen : (∑ check ∈ occupied, maximizingSlots (baseline : ℝ) (upward check : ℝ)) ≤ D := by
    have hsum := Finset.sum_le_sum (fun check (_ : check ∈ occupied) =>
      (maximizingSlots_range (baseline : ℝ) (upward check : ℝ)).2)
    exact (show (∑ check ∈ occupied, maximizingSlots (baseline : ℝ) (upward check : ℝ)) ≤
      occupied.card * 2 by simpa using hsum).trans hroom
  have hmax := aggregate_maximizing_slots occupied slots D
    (fun check => (combined check : ℝ)) (fun check => (upward check : ℝ)) (baseline : ℝ)
    hrange hactual hchosen
  have hleft := scaled_guard_total occupied slots D combined upward baseline (1 : ℝ)
  have hright := scaled_guard_total occupied
    (fun check => maximizingSlots (baseline : ℝ) (upward check : ℝ)) D combined upward baseline (1 : ℝ)
  simp only [one_mul] at hleft hright
  rw [hleft,hright] at hmax
  simpa only [maximizingNatSlots_eq] using hmax
