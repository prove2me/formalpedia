-- Prove2me | solution 1 for SmoothCCP.Feasibility.transfer_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:36:51.604597+00:00
-- url     : https://prove2.me/submissions/d7c30eca-5f0e-430e-b067-efcd00160cc3

import Mathlib
import Definitions.Def_SmoothCCP_Feasibility_Setting

set_option autoImplicit false
open MeasureTheory SmoothCCP.Feasibility

theorem gam_anti (ε : ℝ) (γ : ℝ → ℝ) (hγ : AdmissibleGamma ε γ) {y₁ y₂ : ℝ} (h : y₁ ≤ y₂) :
    Gam ε γ y₂ ≤ Gam ε γ y₁ := by
  have hε := hγ.pos
  have hbd : ∀ y, 0 ≤ Gam ε γ y ∧ Gam ε γ y ≤ 1 := by
    intro y
    unfold Gam
    split_ifs with h1 h2
    · exact ⟨zero_le_one, le_rfl⟩
    · exact hγ.mapsTo y ⟨by linarith, by linarith⟩
    · exact ⟨le_rfl, zero_le_one⟩
  by_cases h1 : y₁ ≤ -ε
  · have : Gam ε γ y₁ = 1 := by simp [Gam, h1]
    rw [this]; exact (hbd y₂).2
  · push_neg at h1
    by_cases h2 : y₁ < ε
    · have e1 : Gam ε γ y₁ = γ y₁ := by simp [Gam, not_le.2 h1, h2]
      by_cases h3 : y₂ < ε
      · have e2 : Gam ε γ y₂ = γ y₂ := by simp [Gam, not_le.2 (by linarith : -ε < y₂), h3]
        rw [e1, e2]
        exact hγ.strictAnti.antitoneOn ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ h
      · have e2 : Gam ε γ y₂ = 0 := by
          simp [Gam, not_le.2 (by linarith : -ε < y₂), h3]
        rw [e2, e1]; exact (hbd y₁).1 |>.trans (by rw [← e1]) 
    · have e1 : Gam ε γ y₁ = 0 := by simp [Gam, not_le.2 h1, h2]
      have e2 : Gam ε γ y₂ = 0 := by
        have : ¬ y₂ < ε := by linarith
        simp [Gam, not_le.2 (by linarith : -ε < y₂), this]
      rw [e1, e2]

theorem solution {n N : ℕ} {Ξ : Type} (C : (Fin n → ℝ) → Ξ → ℝ) (X : Set (Fin n → ℝ))
    (ε : ℝ) (γ : ℝ → ℝ) (hγ : AdmissibleGamma ε γ) (ξs : Fin N → Ξ)
    (L t δ β : ℝ) (hL : 0 < L) (ht : 0 < t)
    (hLip : ∀ i, ∀ x ∈ X, ∀ y ∈ X, |C x (ξs i) - C y (ξs i)| ≤ L * ‖x - y‖)
    (x z : Fin n → ℝ) (hx : x ∈ sampleFeasible C X ε γ ξs (2 * t) (δ - β)) (hz : z ∈ X)
    (hxz : ‖x - z‖ ≤ t / L) :
    1 - δ + β ≤ sampleCdf C ε γ ξs (-t) z := by
  obtain ⟨hxX, hxs⟩ := hx
  have hLt : L * ‖x - z‖ ≤ t := by
    have := mul_le_mul_of_nonneg_left hxz hL.le
    rwa [mul_div_cancel₀ _ hL.ne'] at this
  have key : sampleCdf C ε γ ξs (-(2 * t)) x ≤ sampleCdf C ε γ ξs (-t) z := by
    unfold sampleCdf
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    apply gam_anti ε γ hγ
    have := hLip i x hxX z hz
    have h2 := (abs_le.1 this).1
    linarith
  linarith
