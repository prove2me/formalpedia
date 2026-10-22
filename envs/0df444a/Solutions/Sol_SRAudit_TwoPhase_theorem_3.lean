-- Prove2me | solution 1 for SRAudit.TwoPhase.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:52:31.538989+00:00
-- url     : https://prove2.me/submissions/4d0aeadc-ec5e-4957-aeed-7d342e1eeb84

import Mathlib
import Definitions.Def_SRAudit_TwoPhase_Setting

namespace SRAudit.TwoPhase.Sol3

open SRAudit.TwoPhase

variable {ι : Type} [DecidableEq ι]

theorem state_ext {s t : State ι} (hg : s.g = t.g) (hU : s.U = t.U) : s = t := by
  cases s; cases t; cases hg; cases hU; rfl

theorem V_empty (P : Params) (π : Network ι → ℝ) (γ : State ι) (h : ¬ γ.U.Nonempty) :
    Vstar P π γ = ppValue P π γ := by
  rw [Vstar]; simp [h]

theorem pp_le (P : Params) (π : Network ι → ℝ) (γ : State ι) :
    ppValue P π γ ≤ Vstar P π γ := by
  by_cases h : γ.U.Nonempty
  · rw [Vstar, dif_pos h]; exact le_max_left _ _
  · rw [V_empty P π γ h]

theorem ar_le (P : Params) (π : Network ι → ℝ) (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    -P.a - P.u * P.r + Vstar P π (vet γ i) ≤ Vstar P π γ := by
  have h : γ.U.Nonempty := ⟨i, hi⟩
  conv_rhs => rw [Vstar, dif_pos h]
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach _ ⟨i, hi⟩))
  exact le_max_left _ _

theorem ad_le (P : Params) (π : Network ι → ℝ) (γ : State ι) (i : Supplier ι) (hi : i ∈ γ.U) :
    -P.a + (1 - P.u) * Vstar P π (vet γ i) + P.u * Vstar P π (drop γ i) ≤ Vstar P π γ := by
  have h : γ.U.Nonempty := ⟨i, hi⟩
  conv_rhs => rw [Vstar, dif_pos h]
  refine le_trans ?_ (le_max_right _ _)
  refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_attach _ ⟨i, hi⟩))
  exact le_max_right _ _

theorem V_cases (P : Params) (π : Network ι → ℝ) (γ : State ι) (h : γ.U.Nonempty) :
    Vstar P π γ = ppValue P π γ ∨ ∃ i ∈ γ.U,
      Vstar P π γ = -P.a - P.u * P.r + Vstar P π (vet γ i) ∨
      Vstar P π γ = -P.a + (1 - P.u) * Vstar P π (vet γ i) + P.u * Vstar P π (drop γ i) := by
  rw [Vstar, dif_pos h]
  rcases max_choice (ppValue P π γ) (γ.U.attach.sup' (by simpa using h) (fun i =>
        max (-P.a - P.u * P.r + Vstar P π (vet γ i.val))
            (-P.a + (1 - P.u) * Vstar P π (vet γ i.val) +
              P.u * Vstar P π (drop γ i.val)))) with h1 | h1
  · left; rw [h1]
  · right
    rw [h1]
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (Finset.attach_nonempty_iff.mpr h) (fun i : γ.U =>
        max (-P.a - P.u * P.r + Vstar P π (vet γ i.val))
            (-P.a + (1 - P.u) * Vstar P π (vet γ i.val) +
              P.u * Vstar P π (drop γ i.val)))
    refine ⟨i.val, i.property, ?_⟩
    rw [hi]
    rcases max_choice (-P.a - P.u * P.r + Vstar P π (vet γ i.val))
            (-P.a + (1 - P.u) * Vstar P π (vet γ i.val) +
              P.u * Vstar P π (drop γ i.val)) with h2 | h2
    · left; rw [h2]
    · right; rw [h2]

/-- the value of the rectify-or-produce problem -/
noncomputable def W (P : Params) (π : Network ι → ℝ) (γ : State ι) : ℝ :=
  π γ.g - γ.U.card * crp P

theorem W_vet (P : Params) (π : Network ι → ℝ) (γ : State ι) (j : Supplier ι) (hj : j ∈ γ.U) :
    W P π (vet γ j) = W P π γ + crp P := by
  have h := Finset.card_erase_add_one hj
  have : ((γ.U.erase j).card : ℝ) + 1 = γ.U.card := by exact_mod_cast h
  simp only [W, vet]
  linear_combination (-(crp P)) * this

theorem crp_le_c (P : Params) : crp P ≤ P.a + P.u * P.r := min_le_right _ _
theorem crp_le_e (P : Params) : crp P ≤ P.u * P.w * P.z := min_le_left _ _

theorem pp_le_W (P : Params) (π : Network ι → ℝ) (γ : State ι) :
    ppValue P π γ ≤ W P π γ := by
  simp only [ppValue, W, zeta]
  have := crp_le_e P
  have h0 : (0:ℝ) ≤ γ.U.card := by positivity
  nlinarith

theorem W_le (P : Params) (π : Network ι → ℝ) :
    ∀ n, ∀ γ : State ι, γ.U.card = n → W P π γ ≤ Vstar P π γ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hn
    by_cases h : γ.U.Nonempty
    · by_cases hce : P.u * P.w * P.z ≤ P.a + P.u * P.r
      · have hc : crp P = P.u * P.w * P.z := min_eq_left hce
        have : W P π γ = ppValue P π γ := by simp [W, ppValue, zeta, hc]
        rw [this]; exact pp_le P π γ
      · have hc : crp P = P.a + P.u * P.r := min_eq_right (le_of_not_ge hce)
        obtain ⟨i, hi⟩ := h
        have hlt : (vet γ i).U.card < n := by
          rw [← hn]; simpa [vet] using Finset.card_erase_lt_of_mem hi
        have h1 := ih _ hlt (vet γ i) rfl
        have h2 := W_vet P π γ i hi
        have h3 := ar_le P π γ i hi
        linarith
    · have hU : γ.U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [V_empty P π γ h]; simp [W, ppValue, zeta, hU]

theorem W_le' (P : Params) (π : Network ι → ℝ) (γ : State ι) : W P π γ ≤ Vstar P π γ :=
  W_le P π _ γ rfl

theorem vet_comm (γ : State ι) (i j : Supplier ι) : vet (vet γ i) j = vet (vet γ j) i := by
  refine state_ext rfl ?_
  simp [vet, Finset.erase_right_comm]

theorem mem_drop_U (γ : State ι) (j s : Supplier ι) :
    s ∈ (drop γ j).U ↔ s ∈ γ.U ∧ s ∉ γ.g.dependents j := by
  simp [drop]

theorem drop_vet_of_mem (γ : State ι) (i j : Supplier ι) (h : i ∈ γ.g.dependents j) :
    drop (vet γ i) j = drop γ j := by
  refine state_ext rfl ?_
  ext s
  rw [mem_drop_U, mem_drop_U]
  simp only [vet, Finset.mem_erase]
  constructor
  · rintro ⟨⟨-, hs⟩, hd⟩; exact ⟨hs, hd⟩
  · rintro ⟨hs, hd⟩; exact ⟨⟨fun e => hd (e ▸ h), hs⟩, hd⟩

theorem drop_vet_of_not_mem (γ : State ι) (i j : Supplier ι) :
    drop (vet γ i) j = vet (drop γ j) i := by
  refine state_ext rfl ?_
  ext s
  rw [mem_drop_U]
  show _ ↔ s ∈ ((drop γ j).U.erase i)
  rw [Finset.mem_erase, mem_drop_U]
  simp only [vet, Finset.mem_erase]
  tauto

theorem self_mem_dependents (g : Network ι) (i : Supplier ι) : i ∈ g.dependents i := by
  cases i <;> simp [Network.dependents]

theorem ad_exists (P : Params) (hP : P.Standing) (π : Network ι → ℝ) :
    ∀ n, ∀ γ : State ι, γ.U.card = n → W P π γ < Vstar P π γ →
      ∃ j ∈ γ.U, Qstar P π γ (.ad j) = Vstar P π γ := by
  obtain ⟨ha, hr, hu0, hu1, -, -, -⟩ := hP
  have hc0 : 0 ≤ P.a + P.u * P.r := by positivity
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hn hlt
    have h : γ.U.Nonempty := by
      by_contra h
      have hU : γ.U = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
      rw [V_empty P π γ h] at hlt; simp [W, ppValue, zeta, hU] at hlt
    rcases V_cases P π γ h with hv | ⟨i, hi, hv | hv⟩
    · have := pp_le_W P π γ; linarith
    · -- ar is optimal: push to the vetted state
      set γ' := vet γ i with hγ'
      have hlt' : γ'.U.card < n := by
        rw [← hn]; simpa [γ', vet] using Finset.card_erase_lt_of_mem hi
      have hW' := W_vet P π γ i hi
      have hlt2 : W P π γ' < Vstar P π γ' := by
        have := crp_le_c P; linarith
      obtain ⟨j, hj, hq⟩ := ih _ hlt' γ' rfl hlt2
      have hj' : j ∈ γ.U := (Finset.mem_erase.mp hj).2
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      have hq' : -P.a + (1 - P.u) * Vstar P π (vet γ' j) + P.u * Vstar P π (drop γ' j)
          = Vstar P π γ' := by simpa [Qstar, hj] using hq
      refine ⟨j, hj', ?_⟩
      have hQ : Qstar P π γ (.ad j) =
          -P.a + (1 - P.u) * Vstar P π (vet γ j) + P.u * Vstar P π (drop γ j) := by
        simp [Qstar, hj']
      rw [hQ]
      apply le_antisymm (ad_le P π γ j hj')
      -- lower bounds
      have hX : -(P.a + P.u * P.r) + Vstar P π (vet γ' j) ≤ Vstar P π (vet γ j) := by
        have hi2 : i ∈ (vet γ j).U := Finset.mem_erase.mpr ⟨fun e => hji e.symm, hi⟩
        have := ar_le P π (vet γ j) i hi2
        rw [vet_comm] at this
        linarith
      have hY : -(P.a + P.u * P.r) + Vstar P π (drop γ' j) ≤ Vstar P π (drop γ j) := by
        by_cases hD : i ∈ γ.g.dependents j
        · rw [hγ', drop_vet_of_mem γ i j hD]; linarith
        · have hi2 : i ∈ (drop γ j).U := (mem_drop_U γ j i).mpr ⟨hi, hD⟩
          have := ar_le P π (drop γ j) i hi2
          rw [hγ', drop_vet_of_not_mem γ i j]
          linarith
      have e1 : 0 ≤ 1 - P.u := by linarith
      have k1 := mul_le_mul_of_nonneg_left hX e1
      have k2 := mul_le_mul_of_nonneg_left hY hu0.le
      nlinarith
    · exact ⟨i, hi, by simp [Qstar, hi, hv]⟩

end SRAudit.TwoPhase.Sol3

open SRAudit.TwoPhase SRAudit.TwoPhase.Sol3 in
theorem solution {ι : Type} [DecidableEq ι] (P : Params)
    (hP : P.Standing) (π : Network ι → ℝ) :
    ∃ ξ : Policy ι, IsOptimal P π ξ ∧
      (∀ (γ : State ι) (i : Supplier ι), ξ γ = .ar i →
        P.a + P.u * P.r ≤ P.u * P.w * P.z ∧
        (∀ j ∈ γ.U, Qstar P π γ (.ar j) = Vstar P π γ ∧
          ((vet γ j).U.Nonempty → ∃ k, ξ (vet γ j) = .ar k))) ∧
      (∀ γ : State ι, ξ γ = .pp → γ.U.Nonempty →
        P.u * P.w * P.z ≤ P.a + P.u * P.r) := by
  classical
  have hc0 : 0 ≤ P.a + P.u * P.r := by
    obtain ⟨ha, hr, hu0, -⟩ := hP; positivity
  -- the policy
  let ξ : Policy ι := fun γ =>
    if h : W P π γ < Vstar P π γ then .ad (Classical.choose (ad_exists P hP π _ γ rfl h))
    else if h2 : P.a + P.u * P.r ≤ P.u * P.w * P.z ∧ γ.U.Nonempty then .ar h2.2.choose
    else .pp
  -- key fact: in a non-dropping state with c ≤ e, every ar is optimal
  have key : ∀ γ : State ι, ¬ W P π γ < Vstar P π γ → P.a + P.u * P.r ≤ P.u * P.w * P.z →
      ∀ j ∈ γ.U, Qstar P π γ (.ar j) = Vstar P π γ ∧
        ¬ W P π (vet γ j) < Vstar P π (vet γ j) := by
    intro γ hn hce j hj
    have hc : crp P = P.a + P.u * P.r := min_eq_right hce
    have h1 := W_le' P π γ
    have h2 := W_le' P π (vet γ j)
    have h3 := W_vet P π γ j hj
    have h4 := ar_le P π γ j hj
    have hq : Qstar P π γ (.ar j) = -P.a - P.u * P.r + Vstar P π (vet γ j) := by
      simp [Qstar, hj]
    refine ⟨?_, ?_⟩
    · rw [hq]; linarith
    · intro hl; linarith
  refine ⟨ξ, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro γ
    simp only [ξ]
    split_ifs with h h2
    · exact (Classical.choose_spec (ad_exists P hP π _ γ rfl h)).1
    · exact h2.2.choose_spec
    · trivial
  · intro γ
    simp only [ξ]
    split_ifs with h h2
    · exact (Classical.choose_spec (ad_exists P hP π _ γ rfl h)).2
    · exact (key γ h h2.1 _ h2.2.choose_spec).1
    · show ppValue P π γ = Vstar P π γ
      by_cases hU : γ.U.Nonempty
      · have hce : ¬ P.a + P.u * P.r ≤ P.u * P.w * P.z := fun hh => h2 ⟨hh, hU⟩
        have hc : crp P = P.u * P.w * P.z := min_eq_left (le_of_not_ge hce)
        have : W P π γ = ppValue P π γ := by simp [W, ppValue, zeta, hc]
        have := W_le' P π γ
        linarith
      · exact (V_empty P π γ hU).symm
  · intro γ i hi
    simp only [ξ] at hi
    split_ifs at hi with h h2
    refine ⟨h2.1, fun j hj => ⟨(key γ h h2.1 j hj).1, fun hne => ?_⟩⟩
    have hn := (key γ h h2.1 j hj).2
    simp only [ξ]
    rw [dif_neg hn, dif_pos ⟨h2.1, hne⟩]
    exact ⟨_, rfl⟩
  · intro γ hpp hU
    simp only [ξ] at hpp
    split_ifs at hpp with h h2
    by_contra hce
    exact h2 ⟨le_of_not_ge hce, hU⟩
