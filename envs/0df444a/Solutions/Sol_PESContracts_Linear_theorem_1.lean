-- Prove2me | solution 1 for PESContracts.Linear.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T16:47:05.031122+00:00
-- url     : https://prove2.me/submissions/dd2784d3-37c7-4b9f-96f9-e008a918fe13

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
import Theorems.Thm_PESContracts_Linear_linear_best_response
import Theorems.Thm_PESContracts_Linear_rent_free_upper_bound
import Theorems.Thm_PESContracts_Linear_pointwise_dominance
open MeasureTheory
open PESContracts.Linear

theorem solution (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : μ M.typesᶜ = 0) :
    (∀ aL : ℝ → ℝ, IsLinearBestResponse M (k / 2) aL →
      ∀ C : DirectContract, C.Feasible M →
        Integrable C.a μ → Integrable C.P μ →
        C.payoff k μ ≤ 2 * ∫ θ, (k - k / 2) * aL θ ∂μ) ∧
    (∀ C : DirectContract, C.Feasible M →
        Integrable C.a μ → Integrable C.P μ →
        C.payoff k μ ≤ 2 * ObjLstar M k μ) := by
  obtain ⟨ha0, hh, hlo, hlohi, hhi⟩ := hM
  -- almost every point is a type
  have hae : ∀ᵐ θ ∂μ, θ ∈ M.types := by
    rw [ae_iff]; exact hμ
  have hunit : ∀ θ ∈ M.types, θ ∈ Set.Icc (0:ℝ) 1 := by
    intro θ hθ; exact ⟨le_trans hlo hθ.1, le_trans hθ.2 hhi⟩
  -- continuity of the closed-form action in θ
  have hcont : ∀ p : ℝ, Continuous (fun θ => linAction M p θ) := by
    intro p; unfold linAction; fun_prop
  -- a.e. bounds for the closed-form action at nonnegative prices
  have hbd : ∀ p : ℝ, 0 ≤ p → ∀ᵐ θ ∂μ, linAction M p θ ∈ Set.Icc 0 M.a0 := by
    intro p hp
    filter_upwards [hae] with θ hθ
    exact (linear_best_response M ⟨ha0, hh, hlo, hlohi, hhi⟩ p hp θ (hunit θ hθ)).1
  have hint : ∀ p : ℝ, 0 ≤ p → Integrable (fun θ => linAction M p θ) μ := by
    intro p hp
    refine (integrable_const M.a0).mono' (hcont p).aestronglyMeasurable ?_
    filter_upwards [hbd p hp] with θ hθ
    rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  have hp2 : (0:ℝ) ≤ k / 2 := by linarith
  -- key bound: payoff ≤ 2 * ∫ (k - k/2) * linAction
  have key : ∀ C : DirectContract, C.Feasible M →
      Integrable C.a μ → Integrable C.P μ →
      C.payoff k μ ≤ 2 * ∫ θ, (k - k / 2) * linAction M (k / 2) θ ∂μ := by
    intro C hC hCa hCP
    have h1 := rent_free_upper_bound M ⟨ha0, hh, hlo, hlohi, hhi⟩ k μ hμ C hC hCa hCP
    refine le_trans h1 ?_
    rw [← integral_const_mul]
    have hRint : Integrable (fun θ => 2 * ((k - k / 2) * linAction M (k / 2) θ)) μ :=
      ((hint _ hp2).const_mul (k - k / 2)).const_mul 2
    by_cases hg : Integrable (fun θ => k * C.a θ - cost M.h (C.a θ - θ * M.a0)) μ
    · apply integral_mono_ae hg hRint
      filter_upwards [hae] with θ hθ
      exact pointwise_dominance M ⟨ha0, hh, hlo, hlohi, hhi⟩ k hk θ (hunit θ hθ) (C.a θ)
        (hC θ hθ).1
    · rw [integral_undef hg]
      apply integral_nonneg_of_ae
      filter_upwards [hbd _ hp2] with θ hθ
      have : 0 ≤ k - k / 2 := by linarith
      have := mul_nonneg this hθ.1
      simp only [Pi.zero_apply]; linarith
  refine ⟨?_, ?_⟩
  · intro aL haL C hC hCa hCP
    refine le_trans (key C hC hCa hCP) (le_of_eq ?_)
    congr 1
    apply integral_congr_ae
    filter_upwards [hae] with θ hθ
    have hbr := linear_best_response M ⟨ha0, hh, hlo, hlohi, hhi⟩ (k / 2) hp2 θ (hunit θ hθ)
    have heq : aL θ = linAction M (k / 2) θ :=
      hbr.2.2 (by linarith) (aL θ) (haL θ hθ).1 ((haL θ hθ).2 _ hbr.1)
    simp [heq]
  · intro C hC hCa hCP
    refine le_trans (key C hC hCa hCP) ?_
    have hObj : ∫ θ, (k - k / 2) * linAction M (k / 2) θ ∂μ = ObjL M k μ (k / 2) := by
      unfold ObjL; rw [integral_const_mul]
    rw [hObj]
    have hBdd : BddAbove (ObjL M k μ '' Set.Ici 0) := by
      refine ⟨k * M.a0, ?_⟩
      rintro _ ⟨p, hp, rfl⟩
      have hp' : (0:ℝ) ≤ p := hp
      unfold ObjL
      have hI0 : 0 ≤ ∫ θ, linAction M p θ ∂μ := by
        apply integral_nonneg_of_ae
        filter_upwards [hbd p hp'] with θ hθ; exact hθ.1
      have hI1 : ∫ θ, linAction M p θ ∂μ ≤ M.a0 := by
        have : ∫ θ, linAction M p θ ∂μ ≤ ∫ _θ, M.a0 ∂μ :=
          integral_mono_ae (hint p hp') (integrable_const _)
            (by filter_upwards [hbd p hp'] with θ hθ; exact hθ.2)
        simpa using this
      by_cases hkp : 0 ≤ k - p
      · nlinarith
      · nlinarith
    have : ObjL M k μ (k / 2) ≤ ObjLstar M k μ :=
      le_csSup hBdd ⟨k / 2, hp2, rfl⟩
    linarith
