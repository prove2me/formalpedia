-- Prove2me | solution 1 for WhenToTrustYourModel.markov_tv_bound
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:42:21.974893+00:00
-- url     : https://prove2.me/submissions/8b5e108a-205c-4d1e-874f-9b2cc9ca0460

import Mathlib
import Definitions.Def_WhenToTrustYourModel_Basic
set_option autoImplicit false
open Finset
namespace WhenToTrustYourModel

lemma mtv_nonneg {S : Type*} [Fintype S] (μ₀ : S → ℝ) (hμ₀ : IsDist μ₀)
    (K : ℕ → S → S → ℝ) (hK : ∀ t s, IsDist (K t s)) : ∀ t s, 0 ≤ chainDist μ₀ K t s := by
  intro t
  induction t with
  | zero => intro s; exact hμ₀.1 s
  | succ t ih =>
    intro s'
    simp only [chainDist]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (ih s) ((hK t s).1 s')

theorem markov_tv_bound {S : Type*} [Fintype S]
    (μ₀ : S → ℝ) (hμ₀ : IsDist μ₀)
    (K₁ K₂ : ℕ → S → S → ℝ) (hK₁ : ∀ t s, IsDist (K₁ t s)) (hK₂ : ∀ t s, IsDist (K₂ t s))
    (δ : ℝ) (hδ : ∀ t, ∑ s, chainDist μ₀ K₁ t s * tvDist (K₁ t s) (K₂ t s) ≤ δ)
    (t : ℕ) :
    tvDist (chainDist μ₀ K₁ t) (chainDist μ₀ K₂ t) ≤ t * δ := by
  have hnn := mtv_nonneg μ₀ hμ₀ K₁ hK₁
  induction t with
  | zero => simp [tvDist, chainDist]
  | succ t ih =>
    set a := chainDist μ₀ K₁ t
    set b := chainDist μ₀ K₂ t
    have hstep : ∀ s', |chainDist μ₀ K₁ (t+1) s' - chainDist μ₀ K₂ (t+1) s'| ≤
        ∑ s, a s * |K₁ t s s' - K₂ t s s'| + ∑ s, |a s - b s| * K₂ t s s' := by
      intro s'
      simp only [chainDist]
      have : ∑ s, chainDist μ₀ K₁ t s * K₁ t s s' - ∑ s, chainDist μ₀ K₂ t s * K₂ t s s' =
          ∑ s, a s * (K₁ t s s' - K₂ t s s') + ∑ s, (a s - b s) * K₂ t s s' := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [a, b]; ring
      rw [this]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (hnn t s)]
      · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [abs_mul, abs_of_nonneg ((hK₂ t s).1 s')]
    have hsum := Finset.sum_le_sum fun s' (_ : s' ∈ Finset.univ) => hstep s'
    rw [Finset.sum_add_distrib, Finset.sum_comm, Finset.sum_comm (f := fun s' s => |a s - b s| * K₂ t s s')] at hsum
    have e1 : ∑ y, ∑ x, a y * |K₁ t y x - K₂ t y x| = 2 * ∑ s, a s * tvDist (K₁ t s) (K₂ t s) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum]; unfold tvDist; ring
    have e2 : ∑ y, ∑ x, |a y - b y| * K₂ t y x = 2 * tvDist a b := by
      unfold tvDist
      rw [show (2:ℝ) * (1/2 * ∑ x, |a x - b x|) = ∑ x, |a x - b x| by ring]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← Finset.mul_sum, (hK₂ t s).2, mul_one]
    rw [e1, e2] at hsum
    have h1 : ∑ s, a s * tvDist (K₁ t s) (K₂ t s) ≤ δ := hδ t
    have e3 : tvDist a b = 1/2 * ∑ x, |a x - b x| := rfl
    unfold tvDist at ih ⊢
    push_cast
    linarith

end WhenToTrustYourModel
open WhenToTrustYourModel in
theorem solution {S : Type*} [Fintype S]
    (μ₀ : S → ℝ) (hμ₀ : IsDist μ₀)
    (K₁ K₂ : ℕ → S → S → ℝ) (hK₁ : ∀ t s, IsDist (K₁ t s)) (hK₂ : ∀ t s, IsDist (K₂ t s))
    (δ : ℝ) (hδ : ∀ t, ∑ s, chainDist μ₀ K₁ t s * tvDist (K₁ t s) (K₂ t s) ≤ δ)
    (t : ℕ) :
    tvDist (chainDist μ₀ K₁ t) (chainDist μ₀ K₂ t) ≤ t * δ :=
  markov_tv_bound μ₀ hμ₀ K₁ K₂ hK₁ hK₂ δ hδ t
