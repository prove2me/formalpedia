-- Prove2me | solution 1 for StatefulPricing.thm_3_6_proof_II
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:30:56.898196+00:00
-- url     : https://prove2.me/submissions/9a90c94c-b5b4-4173-91d7-78d4296e0952

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Aux_StatefulPricing_II
open StatefulPricing

lemma demand_spec {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) :
    I.demand rank t p = ∅ ∨ (I.demand rank t p ⊆ I.active t ∧
      ∀ B ⊆ I.active t, I.utility t p B ≤ I.utility t p (I.demand rank t p)) := by
  unfold Instance.demand
  dsimp only
  split
  · rename_i h
    obtain ⟨hmem, _⟩ := Classical.choose_spec (Finset.exists_min_image _ rank h)
    rw [Finset.mem_filter, Finset.mem_powerset] at hmem
    right
    exact ⟨hmem.1, fun B hB => hmem.2 B (Finset.mem_powerset.2 hB)⟩
  · left; rfl

lemma demand_ones {T C W : ℕ} (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ)
    (ht1 : 1 ≤ t) (htT : t ≤ T) : I.demand rank t (fun _ => 1) = ∅ := by
  rcases demand_spec rank I t (fun _ => 1) with h | ⟨hsub, hbest⟩
  · exact h
  · set A := I.demand rank t (fun _ => 1) with hA
    by_contra hne
    have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.2 hne
    have h0 := hbest ∅ (Finset.empty_subset _)
    unfold Instance.utility at h0
    rw [I.v_empty, Finset.sum_empty, sub_zero] at h0
    have hv := I.v_lt_one t ht1 htT A hsub
    have hcard : (1 : ℝ) ≤ ∑ i ∈ A, (1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast Finset.card_pos.2 hAne
    linarith

end Aux_StatefulPricing_II

open StatefulPricing Aux_StatefulPricing_II in
theorem solution {T C W : ℕ} (c : Chase T C W) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t < tfinal → c.Missing t → c.coin t = true →
      c.phi (t + 1) < c.phi t := by
  classical
  intro t ht _ hmiss hcoin
  obtain ⟨i0, hi0bad, hi0D⟩ := hmiss
  set D := c.I.demand c.rank t (c.polPrice t) with hD
  have hbad : ∀ s i, i ∈ c.bad s ↔ i ∈ c.I.active s ∧ c.inv s i < c.polInv s i := by
    intro s i; unfold Chase.bad; rw [Finset.mem_filter]
  have hactive : ∀ s i, i ∈ c.I.active s ↔ i ∈ c.I.R ∧ c.I.ta i ≤ s ∧ s ≤ c.I.te i := by
    intro s i; unfold Instance.active; rw [Finset.mem_filter]
  have hi0act := ((hbad t i0).1 hi0bad).1
  obtain ⟨hR, hta, hte⟩ := (hactive t i0).1 hi0act
  have ht1 : 1 ≤ t := le_trans (c.I.one_le_ta i0 hR) hta
  have htT : t ≤ T := le_trans hte (c.I.te_le_T i0 hR)
  have hinv : c.inv (t + 1) = c.I.step t (c.inv t) ∅ := by
    have e : t + 1 - c.tinit = (t - c.tinit) + 1 := by omega
    unfold Chase.inv
    rw [e]
    show c.I.step (c.tinit + (t - c.tinit)) (c.invOff (t - c.tinit))
      (c.I.demand c.rank (c.tinit + (t - c.tinit))
        (c.price (c.tinit + (t - c.tinit)) (c.invOff (t - c.tinit)))) = _
    have e2 : c.tinit + (t - c.tinit) = t := by omega
    rw [e2]
    have hp : c.price t (c.invOff (t - c.tinit)) = fun _ => 1 := by
      unfold Chase.price; rw [if_pos hcoin]
    rw [hp, demand_ones c.rank c.I t ht1 htT]
  have hpol : c.polInv (t + 1) = c.I.step t (c.polInv t) D := by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    rfl
  -- pointwise facts
  set f : ℕ → ℤ := fun i => (c.polInv t i : ℤ) - (c.inv t i : ℤ) - (if i ∈ D then 1 else 0)
    with hf
  have key : ∀ i ∈ c.bad (t + 1), i ∈ c.bad t ∧
      ((c.polInv (t + 1) i : ℤ) - (c.inv (t + 1) i : ℤ)) = f i := by
    intro i hi
    obtain ⟨hA1, hlt⟩ := (hbad (t + 1) i).1 hi
    by_cases hA0 : i ∈ c.I.active t
    · have hI : c.inv (t + 1) i = c.inv t i := by
        rw [hinv]; simp [Instance.step, hA1, hA0]
      by_cases hiD : i ∈ D
      · have hP : c.polInv (t + 1) i = c.polInv t i - 1 := by
          rw [hpol]; simp [Instance.step, hA1, hA0, hiD]
        rw [hI, hP] at hlt
        refine ⟨(hbad t i).2 ⟨hA0, by omega⟩, ?_⟩
        rw [hI, hP, hf]
        simp only [hiD, if_true]
        push_cast [show 1 ≤ c.polInv t i by omega]
        ring
      · have hP : c.polInv (t + 1) i = c.polInv t i := by
          rw [hpol]; simp [Instance.step, hA1, hA0, hiD]
        rw [hI, hP] at hlt
        refine ⟨(hbad t i).2 ⟨hA0, hlt⟩, ?_⟩
        rw [hI, hP, hf]
        simp only [hiD, if_false]
        ring
    · exfalso
      have hI : c.inv (t + 1) i = c.I.cap i := by
        rw [hinv]; simp [Instance.step, hA1, hA0]
      have hP : c.polInv (t + 1) i = c.I.cap i := by
        rw [hpol]; simp [Instance.step, hA1, hA0]
      rw [hI, hP] at hlt
      exact lt_irrefl _ hlt
  have h1 : c.phi (t + 1) = ∑ i ∈ c.bad (t + 1), f i := by
    unfold Chase.phi
    exact Finset.sum_congr rfl (fun i hi => (key i hi).2)
  have h2 : ∑ i ∈ c.bad (t + 1), f i ≤ ∑ i ∈ c.bad t, f i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => (key i hi).1)
    intro i hi _
    have := ((hbad t i).1 hi).2
    simp only [hf]
    split_ifs <;> omega
  have h3 : ∑ i ∈ c.bad t, f i
      = c.phi t - ∑ i ∈ c.bad t, (if i ∈ D then (1 : ℤ) else 0) := by
    unfold Chase.phi
    rw [hf, ← Finset.sum_sub_distrib]
  have h4 : (1 : ℤ) ≤ ∑ i ∈ c.bad t, (if i ∈ D then (1 : ℤ) else 0) := by
    have := Finset.single_le_sum (f := fun i => if i ∈ D then (1 : ℤ) else 0)
      (fun i _ => by split_ifs <;> norm_num) hi0bad
    simpa [hi0D] using this
  linarith
