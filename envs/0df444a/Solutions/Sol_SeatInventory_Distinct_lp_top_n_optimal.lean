-- Prove2me | solution 1 for SeatInventory.Distinct.lp_top_n_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T15:12:21.711976+00:00
-- url     : https://prove2.me/submissions/28758b96-6928-43a2-8db5-bf1216e4ef35

import Mathlib
import Definitions.Def_SeatInventory_Distinct_DemandModel
import Definitions.Def_SeatInventory_Distinct_MarginalAllocation

set_option autoImplicit false

open SeatInventory.Distinct in
theorem lpTopN_aux_sum_ind {α : Type*} [DecidableEq α] (D T : Finset α) (hTD : T ⊆ D) :
    ∑ a ∈ D, (if a ∈ T then (1 : ℝ) else 0) = (T.card : ℝ) := by
  rw [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hTD]

open SeatInventory.Distinct in
theorem lpTopN_aux_general {α : Type*} [DecidableEq α] (m : α → ℝ) (D T : Finset α) (n : ℕ)
    (hm : ∀ a ∈ D, 0 ≤ m a) (hT : IsTopN m D T n) (X : α → ℝ) (hX : IsLPFeasible D n X) :
    lpObjective m D X ≤ lpObjective m D (fun a => if a ∈ T then (1 : ℝ) else 0) := by
  obtain ⟨hTD, hcard, htop⟩ := hT
  obtain ⟨hX01, hXsum⟩ := hX
  -- threshold
  obtain ⟨θ, hθ0, hθT, hθD⟩ : ∃ θ : ℝ, 0 ≤ θ ∧ (∀ x ∈ T, θ ≤ m x) ∧
      (∀ y ∈ D, y ∉ T → m y ≤ θ) := by
    by_cases hne : T.Nonempty
    · refine ⟨T.inf' hne m, ?_, ?_, ?_⟩
      · exact (Finset.le_inf'_iff hne m).mpr (fun x hx => hm x (hTD hx))
      · intro x hx; exact Finset.inf'_le m hx
      · intro y hy hyT
        exact (Finset.le_inf'_iff hne m).mpr (fun x hx => htop x hx y hy hyT)
    · refine ⟨∑ a ∈ D, m a, Finset.sum_nonneg hm, ?_, ?_⟩
      · intro x hx; exact absurd ⟨x, hx⟩ hne
      · intro y hy _
        exact Finset.single_le_sum hm hy
  have hpt : ∀ a ∈ D, X a * m a ≤ (if a ∈ T then (1 : ℝ) else 0) * m a +
      θ * (X a - (if a ∈ T then (1 : ℝ) else 0)) := by
    intro a ha
    obtain ⟨h0, h1⟩ := hX01 a ha
    by_cases haT : a ∈ T
    · simp only [haT, if_true]
      have := hθT a haT
      nlinarith
    · simp only [haT, if_false]
      have := hθD a ha haT
      nlinarith
  unfold lpObjective
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    lpTopN_aux_sum_ind D T hTD, hcard] at hsum
  have : θ * (∑ a ∈ D, X a - (n : ℝ)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ0 (by linarith)
  linarith

open SeatInventory.Distinct in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) (d : ι → PMF ℕ) (n : ℕ) (T : Finset (ι × ℕ))
    (hT : IsTopN (marginalRevenue f d) (seatPairs ι n) T n) :
    IsLPFeasible (seatPairs ι n) n (fun a => if a ∈ T then (1 : ℝ) else 0) ∧
    ∀ X : ι × ℕ → ℝ, IsLPFeasible (seatPairs ι n) n X →
      lpObjective (marginalRevenue f d) (seatPairs ι n) X ≤
        lpObjective (marginalRevenue f d) (seatPairs ι n)
          (fun a => if a ∈ T then (1 : ℝ) else 0) := by
  have hm : ∀ a ∈ seatPairs ι n, 0 ≤ marginalRevenue f d a := by
    intro a _
    unfold marginalRevenue emsr tailProb
    exact mul_nonneg (hf a.1) ENNReal.toReal_nonneg
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a _
    show 0 ≤ (if a ∈ T then (1:ℝ) else 0) ∧ (if a ∈ T then (1:ℝ) else 0) ≤ 1
    split_ifs <;> norm_num
  · rw [lpTopN_aux_sum_ind _ T hT.1, hT.2.1]
  · intro X hX
    exact lpTopN_aux_general _ _ T n hm hT X hX
