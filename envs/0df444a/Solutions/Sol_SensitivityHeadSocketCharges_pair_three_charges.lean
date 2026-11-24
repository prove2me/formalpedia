-- Prove2me | solution 1 for SensitivityHeadSocketCharges.pair_three_charges
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-11-24T20:20:04.033707+00:00
-- url     : https://prove2.me/submissions/5b227355-4630-47d8-967f-432e4138265e

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace SensitivityHeadSocketCharges
end SensitivityHeadSocketCharges
namespace SensitivityJointEvents
end SensitivityJointEvents
namespace SensitivityProfile456
end SensitivityProfile456
namespace SensitivityRankedConstruction
end SensitivityRankedConstruction

section


/-!
At a high head, an incoming guard repair may share a physical child with an
own target repair. The union can use J for the same identity, or a single M
loss for different identities. The own fee may already include a directional
improvement, so these bounds compose with the paired orientation maximum.
-/
namespace SensitivityHeadSocketCharges

noncomputable section
open scoped Classical
open SensitivityRankedConstruction SensitivityProfile456 SensitivityJointEvents
set_option autoImplicit false

variable {I Color : Type} {L core : ℕ} [Fintype I]







theorem one_incoming_pair_charge (own incoming : Bool → Finset I)
    (base combined : Bool → ℝ)
    (hbase : ∀ s, ((own s).card : ℝ) ≤ base s)
    (hcombined : ∀ s, ((own s ∪ incoming s).card : ℝ) ≤ combined s)
    (hone : ∃ s, incoming (!s) = ∅) :
    ((own false ∪ incoming false).card : ℝ) + ((own true ∪ incoming true).card : ℝ) ≤
      max (combined false + base true) (base false + combined true) := by
  obtain ⟨s,hs⟩ := hone
  cases s
  · simp only [Bool.not_false] at hs
    rw [hs,Finset.union_empty]
    exact (add_le_add (hcombined false) (hbase true)).trans (le_max_left _ _)
  · simp only [Bool.not_true] at hs
    rw [hs,Finset.union_empty]
    exact (add_le_add (hbase false) (hcombined true)).trans (le_max_right _ _)





end
end SensitivityHeadSocketCharges

end

/-! The three source coefficients correspond to no incoming macro, one
incoming macro, or at least two incoming macros at a paired high head. -/
open SensitivityHeadSocketCharges
open scoped Classical BigOperators
set_option autoImplicit false
variable {I : Type} [Fintype I]

theorem solution (scale : ℝ) (hscale : 0 ≤ scale)
    (own incoming : Bool → Finset I) (base combined : Bool → ℕ)
    (kind hits : ℕ) (hhits : hits ≤ 2) (cf : Array ℕ)
    (hbase : ∀ side, ((own side).card : ℝ) ≤ scale * (base side : ℕ))
    (hcombined : ∀ side, ((own side ∪ incoming side).card : ℝ) ≤ scale * (combined side : ℕ))
    (hzero : hits = 0 → ∀ side, incoming side = ∅)
    (hone : hits ≤ 1 → ∃ side, incoming (!side) = ∅)
    (hcf0 : base false + base true ≤ cf[3*kind]?.getD 0)
    (hcf1 : max (combined false + base true) (base false + combined true) ≤ cf[3*kind+1]?.getD 0)
    (hcf2 : combined false + combined true ≤ cf[3*kind+2]?.getD 0) :
    (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) ≤
      scale * (cf[3*kind+hits]?.getD 0 : ℕ) := by
  have hu : (Finset.univ : Finset Bool) = {false,true} := by decide
  have hsum : (∑ side : Bool, ((own side ∪ incoming side).card : ℝ)) =
      ((own false ∪ incoming false).card : ℝ) + ((own true ∪ incoming true).card : ℝ) := by
    simp [hu]
  rw [hsum]
  have hcases : hits = 0 ∨ hits = 1 ∨ hits = 2 := by omega
  rcases hcases with rfl | rfl | rfl
  · rw [hzero rfl false,hzero rfl true,Finset.union_empty,Finset.union_empty,Nat.add_zero]
    have hb := add_le_add (hbase false) (hbase true)
    rw [← mul_add] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcf0) hscale)
  · have hb := one_incoming_pair_charge own incoming
      (fun side => scale * (base side : ℕ)) (fun side => scale * (combined side : ℕ))
      hbase hcombined (hone le_rfl)
    refine hb.trans (max_le ?_ ?_)
    · rw [← mul_add,← Nat.cast_add]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((le_max_left _ _).trans hcf1)) hscale
    · rw [← mul_add,← Nat.cast_add]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ((le_max_right _ _).trans hcf1)) hscale
  · have hb := add_le_add (hcombined false) (hcombined true)
    rw [← mul_add] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hcf2) hscale)
