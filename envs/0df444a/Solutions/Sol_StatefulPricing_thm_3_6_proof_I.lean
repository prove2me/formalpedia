-- Prove2me | solution 1 for StatefulPricing.thm_3_6_proof_I
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:39:34.165437+00:00
-- url     : https://prove2.me/submissions/bdff8849-3ac0-4985-8cdc-b6937cb2c102

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Aux_SP_thm36
open StatefulPricing

theorem traj_le {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W)
    (rule : ℕ → (ℕ → ℕ) → (ℕ → ℝ)) : ∀ t i, I.traj rank rule t i ≤ I.cap i := by
  intro t
  induction t with
  | zero =>
    intro i; simp only [Instance.traj, Instance.initInv]; split_ifs <;> omega
  | succ t ih =>
    intro i
    cases t with
    | zero => simp only [Instance.traj, Instance.initInv]; split_ifs <;> omega
    | succ s =>
      simp only [Instance.traj]
      unfold Instance.step
      have := ih i
      split_ifs <;> omega

theorem active_sub {T C W : ℕ} (I : Instance T C W) (t : ℕ) : I.active t ⊆ I.R :=
  Finset.filter_subset _ _

theorem active_empty {T C W : ℕ} (I : Instance T C W) (t : ℕ) (h : ¬ (1 ≤ t ∧ t ≤ T)) :
    I.active t = ∅ := by
  unfold Instance.active
  apply Finset.filter_false_of_mem
  intro i hi ⟨h1, h2⟩
  apply h
  have := I.one_le_ta i hi
  have := I.ta_le_te i hi
  have := I.te_le_T i hi
  omega

end Aux_SP_thm36

open StatefulPricing Aux_SP_thm36 in
theorem solution {T C W : ℕ} (c : Chase T C W) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t ≤ tfinal → 0 ≤ c.phi t ∧ c.phi t ≤ (C * W : ℤ) := by
  intro t _ _
  have hbad : c.bad t ⊆ c.I.active t := by unfold Chase.bad; exact Finset.filter_subset _ _
  have hmem : ∀ i ∈ c.bad t, c.inv t i < c.polInv t i := by
    intro i hi; unfold Chase.bad at hi; exact (Finset.mem_filter.mp hi).2
  constructor
  · unfold Chase.phi
    apply Finset.sum_nonneg
    intro i hi
    have := hmem i hi
    omega
  · by_cases ht : 1 ≤ t ∧ t ≤ T
    · have hcard : (c.bad t).card ≤ W := (Finset.card_le_card hbad).trans
        (c.I.card_active_le_W t ht.1 ht.2)
      have hle : ∀ i ∈ c.bad t, ((c.polInv t i : ℤ) - (c.inv t i : ℤ)) ≤ (C : ℤ) := by
        intro i hi
        have h1 := traj_le c.rank c.I (c.I.policyRule c.γ) t i
        have h2 := c.I.cap_le_C i (active_sub c.I t (hbad hi))
        have h3 : c.polInv t i = c.I.traj c.rank (c.I.policyRule c.γ) t i := rfl
        omega
      unfold Chase.phi
      calc ∑ i ∈ c.bad t, ((c.polInv t i : ℤ) - (c.inv t i : ℤ))
          ≤ ∑ i ∈ c.bad t, (C : ℤ) := Finset.sum_le_sum hle
        _ = (c.bad t).card * (C : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (C * W : ℤ) := by
          have : ((c.bad t).card : ℤ) ≤ W := by exact_mod_cast hcard
          nlinarith
    · have : c.bad t = ∅ := Finset.subset_empty.mp (active_empty c.I t ht ▸ hbad)
      unfold Chase.phi; rw [this, Finset.sum_empty]; positivity
