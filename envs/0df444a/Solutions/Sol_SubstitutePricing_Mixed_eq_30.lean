-- Prove2me | solution 1 for SubstitutePricing.Mixed.eq_30
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:33:27.451101+00:00
-- url     : https://prove2.me/submissions/46f6a5aa-13c4-4ec4-998b-2a43f98e9186

import Mathlib
import Definitions.Def_SubstitutePricing_Mixed_Model

set_option autoImplicit false
open SubstitutePricing.Mixed

theorem solution (M : Model) (hM : M.Assumptions) (x : Fin M.n → ℕ) (r : Fin M.n → ℝ) :
    M.P0 x (M.mix r) = (1 - ∑ i ∈ M.S1 x, M.P x (M.mix r) i) / (1 + M.Θ x) ∧
    ∀ j ∈ M.S2 x, M.P x (M.mix r) j =
      M.θ j * (1 - ∑ i ∈ M.S1 x, M.P x (M.mix r) i) / (1 + M.Θ x) := by
  have hμ := hM.mu_pos
  set e : Fin M.n → ℝ := fun j => Real.exp ((M.a j - M.mix r j) / M.μ) with he
  set e0 : ℝ := Real.exp (M.u0 / M.μ) with he0
  have he0pos : 0 < e0 := Real.exp_pos _
  have hsplit : ∑ j ∈ M.S x, e j = ∑ j ∈ M.S1 x, e j + ∑ j ∈ M.S2 x, e j := by
    unfold Model.S1 Model.S2
    rw [Finset.sum_inter_add_sum_sdiff]
  have hden : M.den x (M.mix r) = ∑ j ∈ M.S1 x, e j + ∑ j ∈ M.S2 x, e j + e0 := by
    unfold Model.den; rw [← hsplit]
  have hS1sub : M.S1 x ⊆ M.S x := Finset.inter_subset_left
  have hS2sub : M.S2 x ⊆ M.S x := Finset.sdiff_subset
  have hdenpos : 0 < M.den x (M.mix r) := by
    unfold Model.den
    have : 0 < e0 := he0pos
    have h2 : 0 ≤ ∑ j ∈ M.S x, Real.exp ((M.a j - M.mix r j) / M.μ) :=
      Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  have hP : ∀ i ∈ M.S1 x, M.P x (M.mix r) i = e i / M.den x (M.mix r) := by
    intro i hi
    unfold Model.P
    rw [if_pos (hS1sub hi)]
  have hsum1 : ∑ i ∈ M.S1 x, M.P x (M.mix r) i = (∑ i ∈ M.S1 x, e i) / M.den x (M.mix r) := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl hP
  have hθ : ∀ j ∈ M.S2 x, M.θ j = e j / e0 := by
    intro j hj
    have hjd : j ∉ M.dyn := (Finset.mem_sdiff.mp hj).2
    have : M.mix r j = M.rfix j := by unfold Model.mix; rw [if_neg hjd]
    simp only [he, he0, Model.θ, this]
    rw [← Real.exp_sub]; congr 1; ring
  have hΘ : M.Θ x = (∑ j ∈ M.S2 x, e j) / e0 := by
    unfold Model.Θ
    rw [Finset.sum_div]; exact Finset.sum_congr rfl hθ
  have h1 : 1 - ∑ i ∈ M.S1 x, M.P x (M.mix r) i =
      (∑ j ∈ M.S2 x, e j + e0) / M.den x (M.mix r) := by
    rw [hsum1]; field_simp; rw [hden]; ring
  have h1Θ : 1 + M.Θ x = (e0 + ∑ j ∈ M.S2 x, e j) / e0 := by
    rw [hΘ]; field_simp
  have hden' : M.den x (M.mix r) ≠ 0 := hdenpos.ne'
  have hpos2 : 0 < e0 + ∑ j ∈ M.S2 x, e j := by
    have : 0 ≤ ∑ j ∈ M.S2 x, e j := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
    linarith
  constructor
  · rw [h1, h1Θ]
    unfold Model.P0
    field_simp
    have h : Real.exp (M.u0 / M.μ) = e0 := rfl
    rw [h]; ring
  · intro j hj
    rw [h1, h1Θ, hθ j hj]
    unfold Model.P
    rw [if_pos (hS2sub hj)]
    field_simp
    have h : Real.exp ((M.a j - M.mix r j) / M.μ) = e j := rfl
    rw [h]; ring
