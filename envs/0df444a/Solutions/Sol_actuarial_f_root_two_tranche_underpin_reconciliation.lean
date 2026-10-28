-- Prove2me | solution 1 for actuarial_f_root_two_tranche_underpin_reconciliation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T20:41:49.632877+00:00
-- url     : https://prove2.me/submissions/7dde4109-33fe-4b37-82d8-adb1ec143d7b

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_f_directEPV
import Definitions.Def_actuarial_f_firstAwardPV
import Definitions.Def_actuarial_f_firstOptionPV
import Definitions.Def_actuarial_f_stateEPV

open ActuarialUnderpinsF

theorem solution
    (n h r g : ℕ) (p : ℕ → ℕ → ℕ → ℝ)
    (disc : ℕ → ℝ) (a b c : ℕ → ℝ) (s : ℕ → ℕ → ℝ)
    (estate : ℕ → ℝ) (g0 g1 : ℕ → ℝ)
    (gs : ℕ → ℕ → ℝ) (ge : ℕ → ℝ)
    (hv : 0 < n ∧
      (∀ z ∈ Finset.range n, ∀ i ∈ Finset.range (h + 1),
        ∀ j ∈ Finset.range (h + 1), 0 ≤ p z i j) ∧
      (∑ z ∈ Finset.range n, ∑ i ∈ Finset.range (h + 1),
        ∑ j ∈ Finset.range (h + 1), p z i j) = 1)
    (hd : ∀ t ∈ Finset.range (h + 1), 0 ≤ disc t)
    (hg : ∀ t ∈ Finset.range (h + 1), 0 ≤ g0 t) :
    directEPV n h r g p disc a b c s estate g0 g1 gs ge =
        stateEPV n h r g p disc a b c s estate g0 g1 gs ge ∧
      max (firstOptionPV n h r p disc a g0)
          (firstOptionPV n h r p disc b g0) ≤
        firstAwardPV n h r p disc a b g0 := by
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
  have sle : ∀ (s : Finset ℕ) (f g : ℕ → ℝ), (∀ x ∈ s, f x ≤ g x) → s.sum f ≤ s.sum g := by
    intro s f g hfg
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact add_le_add (hfg a (Finset.mem_insert_self a s)) (ih fun x hx => hfg x (Finset.mem_insert_of_mem hx))
  have hm : ∀ i t : ℕ, 0 ≤ memberDue r i t := by
    intro i t; unfold memberDue ActuarialJointD.alive; split_ifs <;> norm_num
  refine ⟨hrec, ?_⟩
  unfold firstAwardPV firstOptionPV expect ActuarialJointD.expect
  apply max_le
  · apply sle; intro z hz
    apply sle; intro i hi
    apply sle; intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hv.2.1 z hz i hi j hj)
    apply sle; intro t ht
    refine mul_le_mul_of_nonneg_left ?_ (hd t ht)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (hg t ht)) (hm i t)
  · apply sle; intro z hz
    apply sle; intro i hi
    apply sle; intro j hj
    refine mul_le_mul_of_nonneg_left ?_ (hv.2.1 z hz i hi j hj)
    apply sle; intro t ht
    refine mul_le_mul_of_nonneg_left ?_ (hd t ht)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) (hg t ht)) (hm i t)
