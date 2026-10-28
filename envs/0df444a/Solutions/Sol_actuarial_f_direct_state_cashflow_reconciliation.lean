-- Prove2me | solution 1 for actuarial_f_direct_state_cashflow_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:40.993858+00:00
-- url     : https://prove2.me/submissions/20fea3cf-dc8b-42a1-b7d7-4a6bb516f43c

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_stateEPV

open ActuarialUnderpinsF

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
      stateEPV n h r g p disc a b c s estate g0 g1 gs ge := by
  have msum : ∀ (s : Finset ℕ) (f : ℕ → ℝ) (c : ℝ), c * s.sum f = s.sum (fun x => c * f x) := by
    intro s f c
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, mul_add, ih]
  have scomm : ∀ (s t : Finset ℕ) (f : ℕ → ℕ → ℝ),
      s.sum (fun x => t.sum (f x)) = t.sum (fun y => s.sum (fun x => f x y)) := by
    intro s t f
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.sum_add_distrib, ih]
  have hrec : directEPV n h r g p disc a b c s estate g0 g1 gs ge =
      stateEPV n h r g p disc a b c s estate g0 g1 gs ge := by
    unfold directEPV stateEPV realisedPV expect ActuarialJointD.expect
    simp only [mul_add, msum, ← Finset.sum_add_distrib]
    conv_rhs => rw [scomm]
    refine Finset.sum_congr rfl fun z _ => ?_
    conv_rhs => rw [scomm]
    refine Finset.sum_congr rfl fun i _ => ?_
    conv_rhs => rw [scomm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    unfold totalInstalment memberTrancheOne memberTrancheTwo estateInstalment
    grind
  exact hrec
