-- Prove2me | solution 1 for StaticReusable.Guarantee.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T07:41:36.730622+00:00
-- url     : https://prove2.me/submissions/93626073-8c45-4c19-8b30-0683266e92ec

import Mathlib
import Definitions.Def_StaticReusable_Guarantee_Setting
import Theorems.Thm_StaticReusable_Guarantee_eq_11
import Theorems.Thm_StaticReusable_Guarantee_eq_12
import Theorems.Thm_StaticReusable_Guarantee_service_ratio_eq_R
import Theorems.Thm_StaticReusable_Guarantee_step_2a_C2
import Theorems.Thm_StaticReusable_Guarantee_step_2a_C3
import Theorems.Thm_StaticReusable_Guarantee_combination

open Finset

namespace SolSRGThm1
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

lemma serviceLevel_pos {C : ℕ} {μ Λ : ℝ} (hC : 1 ≤ C) (hμ : 0 < μ) {lam : ℕ → ℝ}
    (hlam : lam ∈ Policies C Λ) : 0 < serviceLevel C μ lam := by
  unfold serviceLevel prob
  have hT := total_pos hμ hlam
  have h := Finset.single_le_sum (f := fun k => weight C μ lam k / ∑ k ∈ Finset.range (C + 1), weight C μ lam k)
    (fun k _ => div_nonneg (weight_nonneg hμ hlam k) hT.le)
    (show C ∈ Finset.Icc 1 C by simp [hC])
  have : 0 < weight C μ lam C / ∑ k ∈ Finset.range (C + 1), weight C μ lam k :=
    div_pos (weight_C_pos lam) hT
  linarith

lemma marketShare_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ}
    (hlam : lam ∈ Policies C Λ) : 0 ≤ marketShare C μ lam := by
  unfold marketShare prob
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg (hlam i hi).1 (div_nonneg (weight_nonneg hμ hlam i) (total_pos hμ hlam).le)

lemma zOf_nonneg {C : ℕ} {μ Λ : ℝ} (hμ : 0 < μ) {lam : ℕ → ℝ} (hlam : lam ∈ Policies C Λ)
    (k : ℕ) (hk : k ∈ Finset.Icc 1 C) : 0 ≤ zOf C μ lam k := by
  unfold zOf
  apply Finset.prod_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj hk
  have := (hlam j (by simp only [Finset.mem_Icc]; omega)).1
  positivity

lemma R_one (z : ℕ → ℝ) (hz : 0 ≤ z 1) : R 1 z = 1 := by
  unfold R uSum xSum zExt a
  simp [Finset.sum_range_succ]
  have : z 1 + 1 ≠ 0 := by linarith
  field_simp
  exact this

lemma R_bound {C : ℕ} (hC : 1 ≤ C) (z : ℕ → ℝ) (hz : ∀ k ∈ Finset.Icc 1 C, 0 ≤ z k) :
    (15 / 19 : ℝ) ≤ R C z := by
  rcases (show C = 1 ∨ C = 2 ∨ C = 3 ∨ 4 ≤ C by omega) with h | h | h | h
  · subst h; rw [R_one z (hz 1 (by simp))]; norm_num
  · subst h
    have := (step_2a_C2 z (hz 1 (by simp)) (hz 2 (by simp))).2
    linarith
  · subst h; exact step_2a_C3 z hz
  · exact (combination h z hz).2.2

end SolSRGThm1

open SolSRGThm1 in
theorem solution {C : ℕ} {μ Λ c α₁ α₂ α₃ : ℝ} {p : ℝ → ℝ}
    (hS : StaticReusable.Guarantee.Standing C μ Λ c p α₁ α₂ α₃) (lamStar : ℕ → ℝ)
    (hpol : lamStar ∈ StaticReusable.Guarantee.Policies C Λ)
    (hopt : IsMaxOn (StaticReusable.Guarantee.value C μ p c α₁ α₂ α₃)
      (StaticReusable.Guarantee.Policies C Λ) lamStar) :
    ∃ l ∈ Set.Icc 0 Λ,
      (0 ≤ StaticReusable.Guarantee.profit C μ p c lamStar →
          (15 / 19 : ℝ) * StaticReusable.Guarantee.profit C μ p c lamStar ≤
            StaticReusable.Guarantee.profit C μ p c (fun _ => l)) ∧
        (15 / 19 : ℝ) * StaticReusable.Guarantee.marketShare C μ lamStar ≤
            StaticReusable.Guarantee.marketShare C μ (fun _ => l) ∧
        (15 / 19 : ℝ) * StaticReusable.Guarantee.serviceLevel C μ lamStar ≤
            StaticReusable.Guarantee.serviceLevel C μ (fun _ => l) := by
  open StaticReusable.Guarantee in
  have hC := hS.one_le_C
  have hμ := hS.μ_pos
  set l := staticRate C μ lamStar with hl
  obtain ⟨hlmem, h12⟩ := eq_12 hS lamStar hpol
  have h11 := eq_11 hμ lamStar hpol
  have hR := service_ratio_eq_R (Λ := Λ) hC hμ lamStar hpol
  have hSL := serviceLevel_pos hC hμ hpol
  have hRb := R_bound hC (zOf C μ lamStar) (fun k hk => zOf_nonneg hμ hpol k hk)
  have hMS := marketShare_nonneg hμ hpol
  rw [← hl] at h12 h11 hR
  have hSLs : serviceLevel C μ (fun _ => l) = R C (zOf C μ lamStar) * serviceLevel C μ lamStar := by
    rw [← hR]; field_simp
  have hSLb : (15 / 19 : ℝ) * serviceLevel C μ lamStar ≤ serviceLevel C μ (fun _ => l) := by
    rw [hSLs]; nlinarith
  refine ⟨l, hlmem, ?_, ?_, hSLb⟩
  · intro hP
    have : (15 / 19 : ℝ) * profit C μ p c lamStar * serviceLevel C μ lamStar ≤
        profit C μ p c (fun _ => l) * serviceLevel C μ lamStar := by nlinarith
    nlinarith
  · have : (15 / 19 : ℝ) * marketShare C μ lamStar * serviceLevel C μ lamStar ≤
        marketShare C μ (fun _ => l) * serviceLevel C μ lamStar := by nlinarith
    nlinarith
