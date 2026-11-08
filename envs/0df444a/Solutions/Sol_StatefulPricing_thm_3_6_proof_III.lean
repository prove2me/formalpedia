-- Prove2me | solution 1 for StatefulPricing.thm_3_6_proof_III
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T02:18:14.685221+00:00
-- url     : https://prove2.me/submissions/a53d3f96-b629-4308-a9dd-64ebcdc8db46

import Mathlib
import Definitions.Def_StatefulPricing_Instance
import Definitions.Def_StatefulPricing_Chase

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace StatefulPricing.Aux_SP

open StatefulPricing StatefulPricing.Instance

variable {T C W : ℕ}

theorem demand_congr (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p q : ℕ → ℝ)
    (h : ∀ i ∈ I.active t, p i = q i) : I.demand rank t p = I.demand rank t q := by
  classical
  have hu : ∀ A ∈ (I.active t).powerset, I.utility t p A = I.utility t q A := by
    intro A hA
    unfold Instance.utility
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact h i (Finset.mem_powerset.mp hA hi)
  have hbest : (I.active t).powerset.filter
      (fun A => ∀ B ∈ (I.active t).powerset, I.utility t p B ≤ I.utility t p A) =
      (I.active t).powerset.filter
      (fun A => ∀ B ∈ (I.active t).powerset, I.utility t q B ≤ I.utility t q A) := by
    apply Finset.filter_congr
    intro A hA
    constructor
    · intro hAll B hB
      rw [← hu A hA, ← hu B hB]; exact hAll B hB
    · intro hAll B hB
      rw [hu A hA, hu B hB]; exact hAll B hB
  unfold Instance.demand
  simp only
  exact congrArg (fun X : Finset (Finset ℕ) =>
    if h : X.Nonempty then Classical.choose (X.exists_min_image rank h) else ∅) hbest

theorem demand_mem (rank : Finset ℕ → ℕ) (I : Instance T C W) (t : ℕ) (p : ℕ → ℝ) :
    I.demand rank t p = ∅ ∨
      (I.demand rank t p ∈ (I.active t).powerset ∧
        ∀ B ∈ (I.active t).powerset, I.utility t p B ≤ I.utility t p (I.demand rank t p)) := by
  classical
  unfold Instance.demand
  simp only
  split_ifs with h
  · right
    have := (Classical.choose_spec (Finset.exists_min_image _ rank h)).1
    rw [Finset.mem_filter] at this
    exact this
  · left; rfl

end StatefulPricing.Aux_SP

open StatefulPricing StatefulPricing.Instance StatefulPricing.Aux_SP in
theorem solution {T C W : ℕ} (c : Chase T C W) (hrank : Function.Injective c.rank)
    (hγ : IsFeasiblePolicy c.γ) (tfinal : ℕ) :
    ∀ t, c.tinit ≤ t → t ≤ tfinal → c.phi t = 0 →
      ∀ t', t < t' → t' ≤ tfinal → c.phi t' = 0 := by
  classical
  -- phi vanishes iff the bad set is empty
  have hphi : ∀ t, c.phi t = 0 ↔ ∀ i ∈ c.I.active t, c.polInv t i ≤ c.inv t i := by
    intro t
    unfold Chase.phi Chase.bad
    constructor
    · intro h i hi
      by_contra hlt
      push_neg at hlt
      have hnn : ∀ j ∈ (c.I.active t).filter (fun i => c.inv t i < c.polInv t i),
          0 ≤ ((c.polInv t j : ℤ) - (c.inv t j : ℤ)) := by
        intro j hj
        have := (Finset.mem_filter.mp hj).2
        have : (c.inv t j : ℤ) < c.polInv t j := by exact_mod_cast this
        linarith
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_filter.mpr ⟨hi, hlt⟩)
      have h2 : (c.inv t i : ℤ) < c.polInv t i := by exact_mod_cast hlt
      linarith
    · intro h
      apply Finset.sum_eq_zero
      intro i hi
      exact absurd (h i (Finset.mem_filter.mp hi).1) (not_le.mpr (Finset.mem_filter.mp hi).2)
  -- recursion for the chase inventory
  have hinv : ∀ s, c.tinit ≤ s → c.inv (s + 1) =
      c.I.step s (c.inv s) (c.I.demand c.rank s (c.price s (c.inv s))) := by
    intro s hs
    unfold Chase.inv
    rw [show s + 1 - c.tinit = (s - c.tinit) + 1 by omega]
    simp only [Chase.invOff]
    rw [Nat.add_sub_cancel' hs]
  -- recursion for the policy inventory
  have hact0 : ∀ i, i ∉ c.I.active 0 := by
    intro i hi
    unfold Instance.active at hi
    rw [Finset.mem_filter] at hi
    have := c.I.one_le_ta i hi.1
    omega
  have hpol : ∀ s, ∀ i, c.polInv (s + 1) i =
      c.I.step s (c.polInv s) (c.I.demand c.rank s (c.polPrice s)) i := by
    intro s i
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      unfold Chase.polInv Instance.policyInv Instance.step
      simp only [Instance.traj]
      rw [if_neg (hact0 i)]
      unfold Instance.initInv
      rfl
    · obtain ⟨r, rfl⟩ : ∃ r, s = r + 1 := ⟨s - 1, by omega⟩
      rfl
  -- the inductive step
  have hstep : ∀ s, c.tinit ≤ s → c.phi s = 0 → c.phi (s + 1) = 0 := by
    intro s hs h0
    rw [hphi] at h0 ⊢
    intro i hi
    rw [hinv s hs, hpol s i]
    unfold Instance.step
    rw [if_pos hi, if_pos hi]
    by_cases hit : i ∈ c.I.active s
    · rw [if_pos hit, if_pos hit]
      have hle := h0 i hit
      have hiR : i ∈ c.I.R ∧ c.I.ta i ≤ s ∧ s ≤ c.I.te i := by
        unfold Instance.active at hit; exact Finset.mem_filter.mp hit
      have hs1 : 1 ≤ s := le_trans (c.I.one_le_ta i hiR.1) hiR.2.1
      have hsT : s ≤ T := le_trans hiR.2.2 (c.I.te_le_T i hiR.1)
      by_cases hcoin : c.coin s = true
      · -- the chase offers nothing for sale
        have hnot : i ∉ c.I.demand c.rank s (c.price s (c.inv s)) := by
          intro hmem
          rcases demand_mem c.rank c.I s (c.price s (c.inv s)) with hD | ⟨hsub, hopt⟩
          · rw [hD] at hmem; exact absurd hmem (Finset.notMem_empty i)
          · set D := c.I.demand c.rank s (c.price s (c.inv s)) with hDdef
            have h1 := hopt ∅ (Finset.empty_mem_powerset _)
            have hsubD : D ⊆ c.I.active s := Finset.mem_powerset.mp hsub
            have hv := c.I.v_lt_one s hs1 hsT D hsubD
            have hp1 : ∀ j, c.price s (c.inv s) j = 1 := by
              intro j; unfold Chase.price; rw [if_pos hcoin]
            unfold Instance.utility at h1
            rw [c.I.v_empty, Finset.sum_empty, sub_zero] at h1
            simp only [hp1, Finset.sum_const, nsmul_eq_mul, mul_one] at h1
            have hcard : (1 : ℝ) ≤ D.card := by
              have : 0 < D.card := Finset.card_pos.mpr ⟨i, hmem⟩
              exact_mod_cast this
            linarith
        rw [if_neg hnot]
        split_ifs <;> omega
      · -- prices agree on the active items
        have hcoin' : c.coin s = false := by simpa using hcoin
        have hagree : ∀ j ∈ c.I.active s, c.price s (c.inv s) j = c.polPrice s j := by
          intro j hj
          unfold Chase.price
          rw [if_neg hcoin]
          unfold Chase.hatPrice
          rw [if_pos ⟨hj, h0 j hj⟩]
        rw [demand_congr c.rank c.I s _ _ hagree]
        split_ifs <;> omega
    · rw [if_neg hit, if_neg hit]
  intro t ht htf h0 t' htt' ht'f
  have key : ∀ k, c.phi (t + k) = 0 := by
    intro k
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      rw [← Nat.add_assoc]
      exact hstep (t + k) (by omega) ih
  have := key (t' - t)
  rwa [Nat.add_sub_cancel' htt'.le] at this
