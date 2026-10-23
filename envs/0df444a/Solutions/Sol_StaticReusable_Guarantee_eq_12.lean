-- Prove2me | solution 1 for StaticReusable.Guarantee.eq_12
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:44:37.969796+00:00
-- url     : https://prove2.me/submissions/96f923ea-da1c-4a19-8d04-10ad73c41d0a

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting

open Finset

namespace SolSRGEq12
open StaticReusable.Guarantee

lemma weight_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ weight C μ lam i := by
  unfold weight
  apply mul_nonneg (by positivity)
  apply Finset.prod_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

lemma weight_C_pos {C : ℕ} {μ : ℝ} (lam : ℕ → ℝ) : 0 < weight C μ lam C := by
  unfold weight
  have : Finset.Icc (C + 1) C = ∅ := by ext; simp
  rw [this, Finset.prod_empty, mul_one]
  exact_mod_cast Nat.descFactorial_self C ▸ Nat.factorial_pos C

lemma total_pos {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ) :
    0 < ∑ k ∈ Finset.range (C + 1), weight C μ lam k := by
  have h := Finset.single_le_sum (f := fun k => weight C μ lam k)
    (fun k _ => weight_nonneg hμ hlam k) (Finset.self_mem_range_succ C)
  linarith [weight_C_pos (C := C) (μ := μ) lam]

lemma prob_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (i : ℕ) : 0 ≤ prob C μ lam i :=
  div_nonneg (weight_nonneg hμ hlam i) (total_pos hμ hlam).le

lemma serviceLevel_pos {C : ℕ} {μ Λ : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ) {lam : ℕ → ℝ}
    (hlam : lam ∈ Policies C Λ) : 0 < serviceLevel C μ lam := by
  unfold serviceLevel
  have h := Finset.single_le_sum (f := fun k => prob C μ lam k)
    (fun k _ => prob_nonneg hμ hlam k) (show C ∈ Finset.Icc 1 C by simp [hC])
  have : 0 < prob C μ lam C := div_pos (weight_C_pos lam) (total_pos hμ hlam)
  linarith

end SolSRGEq12

open SolSRGEq12 in
theorem solution {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : StaticReusable.Guarantee.Standing C μ Λ c p α₁ α₂ α₃) (lam : ℕ → ℝ)
    (hlam : lam ∈ StaticReusable.Guarantee.Policies C Λ) :
    StaticReusable.Guarantee.staticRate C μ lam ∈ Set.Icc 0 Λ ∧
      StaticReusable.Guarantee.profit C μ p c lam *
          StaticReusable.Guarantee.serviceLevel C μ
            (fun _ => StaticReusable.Guarantee.staticRate C μ lam) ≤
        StaticReusable.Guarantee.profit C μ p c
            (fun _ => StaticReusable.Guarantee.staticRate C μ lam) *
          StaticReusable.Guarantee.serviceLevel C μ lam := by
  open StaticReusable.Guarantee in
  have hμ := hS.μ_pos
  have hC := hS.one_le_C
  have hSL := serviceLevel_pos hC hμ hlam
  set S := serviceLevel C μ lam with hSdef
  -- normalized weights
  set w : ℕ → ℝ := fun i => prob C μ lam i / S with hw
  have hw0 : ∀ i ∈ Finset.Icc 1 C, 0 ≤ w i := fun i _ => div_nonneg (prob_nonneg hμ hlam i) hSL.le
  have hw1 : ∑ i ∈ Finset.Icc 1 C, w i = 1 := by
    simp only [hw]; rw [← Finset.sum_div]; exact div_self hSL.ne'
  have hrate : staticRate C μ lam = ∑ i ∈ Finset.Icc 1 C, w i • lam i := by
    unfold staticRate
    rw [show ∑ i ∈ Finset.Icc 1 C, prob C μ lam i = S from rfl]
    simp only [hw, smul_eq_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl; intro i _; ring
  have hmem : staticRate C μ lam ∈ Set.Icc 0 Λ := by
    rw [hrate]
    exact (convex_Icc 0 Λ).sum_mem hw0 hw1 (fun i hi => hlam i hi)
  refine ⟨hmem, ?_⟩
  set l := staticRate C μ lam with hl
  have hlpol : (fun _ => l) ∈ Policies C Λ := fun _ _ => hmem
  have hSs := serviceLevel_pos hC hμ hlpol
  have hJ := hS.concave.le_map_sum hw0 hw1 (fun i hi => hlam i hi)
  rw [← hrate] at hJ
  simp only [smul_eq_mul] at hJ
  have hprof_s : profit C μ p c (fun _ => l) = l * (p l - c) * serviceLevel C μ (fun _ => l) := by
    unfold profit serviceLevel; rw [Finset.mul_sum]
  have hprof : profit C μ p c lam = S * ∑ i ∈ Finset.Icc 1 C, w i * (lam i * (p (lam i) - c)) := by
    unfold profit
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    simp only [hw]; field_simp
  rw [hprof, hprof_s]
  have := mul_le_mul_of_nonneg_left hJ (mul_nonneg hSL.le hSs.le)
  nlinarith
