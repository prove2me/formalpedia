-- Prove2me | solution 1 for ReluMIP.Ideal.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T03:18:24.782831+00:00
-- url     : https://prove2.me/submissions/ea440cf0-2bd2-46aa-84f6-39da88fa03e9

import Mathlib
import Definitions.Def_ReluMIP_Ideal_Setting
import Theorems.Thm_ReluMIP_Ideal_relax6_eq_convexHull

namespace ReluMIP.Ideal

lemma wLb_le {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * Lbrev w L U i ≤ w i * x i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Lbrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h1 h
  · exact mul_le_mul_of_nonpos_left h2 (le_of_lt (not_le.mp h))

lemma le_wUb {η : ℕ} (w L U x : Fin η → ℝ) (hx : x ∈ box L U) (i : Fin η) :
    w i * x i ≤ w i * Ubrev w L U i := by
  obtain ⟨h1, h2⟩ := hx i
  unfold Ubrev
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left h2 h
  · exact mul_le_mul_of_nonpos_left h1 (le_of_lt (not_le.mp h))

lemma mem_relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : affineFn w b x ≤ 0) : (x, (0 : ℝ), (0 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨hf, ?_, hx, le_refl _, le_refl _, zero_le_one⟩
  intro I _
  simp only [rhs6b, sub_zero, mul_one, mul_zero, add_zero]
  exact Finset.sum_nonneg fun i _ => by
    have := wLb_le w L U x hx i
    nlinarith

lemma mem_relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ)
    (hx : x ∈ box L U) (hf : 0 ≤ affineFn w b x) :
    (x, affineFn w b x, (1 : ℝ)) ∈ relax6 w b L U := by
  refine ⟨le_refl _, ?_, hx, hf, zero_le_one, le_refl _⟩
  intro I _
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one]
  have hs : ∑ i ∈ Finset.univ \ I, w i * x i + ∑ i ∈ I, w i * x i = ∑ i, w i * x i :=
    Finset.sum_sdiff (Finset.subset_univ I)
  have : ∑ i ∈ Finset.univ \ I, w i * x i ≤ ∑ i ∈ Finset.univ \ I, w i * Ubrev w L U i :=
    Finset.sum_le_sum fun i _ => le_wUb w L U x hx i
  unfold affineFn
  linarith

lemma relax6_zero {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (0 : ℝ)) ∈ relax6 w b L U) : y = 0 := by
  obtain ⟨_, h6b, _, hy, _⟩ := h
  have := h6b ∅ (Finset.empty_subset _)
  simp [rhs6b] at this
  linarith

lemma relax6_one {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) (x : Fin η → ℝ) (y : ℝ)
    (h : (x, y, (1 : ℝ)) ∈ relax6 w b L U) : y = affineFn w b x := by
  obtain ⟨h6a, h6b, _, _, _⟩ := h
  have := h6b (supp w) (subset_refl _)
  simp only [rhs6b, sub_self, mul_zero, sub_zero, mul_one] at this
  have h0 : ∑ i ∈ Finset.univ \ supp w, w i * Ubrev w L U i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  have h1 : ∑ i ∈ supp w, w i * x i = ∑ i, w i * x i :=
    Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
      have : w i = 0 := by simpa [supp] using hi
      simp [this]
  simp only at h6a
  unfold affineFn at *
  linarith

theorem formulation6 {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ) :
    IsFormulationFor (relax6 w b L U) (reluGraph w b L U) := by
  intro x y
  constructor
  · rintro ⟨hx, hy⟩
    simp only at hx hy
    rcases le_total (affineFn w b x) 0 with h | h
    · refine ⟨0, Or.inl rfl, ?_⟩
      have : y = 0 := by rw [hy, relu, max_eq_left h]
      rw [this]
      exact mem_relax6_zero w b L U x hx h
    · refine ⟨1, Or.inr rfl, ?_⟩
      have : y = affineFn w b x := by rw [hy, relu, max_eq_right h]
      rw [this]
      exact mem_relax6_one w b L U x hx h
  · rintro ⟨z, hz, hm⟩
    refine ⟨hm.2.2.1, ?_⟩
    have h6a : affineFn w b x ≤ y := hm.1
    have hy : 0 ≤ y := hm.2.2.2.1
    simp only
    rcases hz with rfl | rfl
    · have := relax6_zero w b L U x y hm
      subst this
      rw [relu, max_eq_left h6a]
    · have := relax6_one w b L U x y hm
      rw [relu, max_eq_right (this ▸ hy), this]

end ReluMIP.Ideal

open ReluMIP.Ideal in
theorem solution {η : ℕ} (w : Fin η → ℝ) (b : ℝ) (L U : Fin η → ℝ)
    (hLU : ∀ i, L i < U i) (hSA : StrictActivity w b L U) :
    IsFormulationFor (relax6 w b L U) (reluGraph w b L U) ∧ IsIdeal (relax6 w b L U) := by
  refine ⟨formulation6 w b L U, ?_⟩
  intro p hp
  rw [relax6_eq_convexHull w b L U hLU] at hp
  exact (extremePoints_convexHull_subset hp).2
