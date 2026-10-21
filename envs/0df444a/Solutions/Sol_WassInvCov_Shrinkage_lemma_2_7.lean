-- Prove2me | solution 1 for WassInvCov.Shrinkage.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:36:26.628777+00:00
-- url     : https://prove2.me/submissions/01e5d145-3510-499d-aec5-fdf1ce734aa8

import Mathlib
set_option autoImplicit false

theorem solution {E Γ : Type*} [NormedAddCommGroup E] (ϕ : E → Γ → ℝ) (ε₀ : E) :
    ((∀ γ, ContinuousAt (fun ε => ϕ ε γ) ε₀) →
      UpperSemicontinuousAt (fun ε => ⨅ γ, (ϕ ε γ : EReal)) ε₀) ∧
    ((∃ L : ℝ, 0 ≤ L ∧ ∀ ε γ, ϕ ε γ - ϕ ε₀ γ ≥ -L * ‖ε₀ - ε‖) →
      LowerSemicontinuousAt (fun ε => ⨅ γ, (ϕ ε γ : EReal)) ε₀) := by
  constructor
  · intro hc y hy
    obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hy
    obtain ⟨r, h1, h2⟩ := EReal.lt_iff_exists_real_btwn.mp hγ
    have hr : (ϕ ε₀ γ) < r := by exact_mod_cast h1
    have hev : ∀ᶠ ε in nhds ε₀, ϕ ε γ < r := (hc γ).eventually (gt_mem_nhds hr)
    filter_upwards [hev] with ε hε
    calc (⨅ γ, (ϕ ε γ : EReal)) ≤ (ϕ ε γ : EReal) := iInf_le _ γ
      _ < (r : EReal) := by exact_mod_cast hε
      _ < y := h2
  · rintro ⟨L, hL, h⟩ y hy
    obtain ⟨r, hyr, hrΦ⟩ := EReal.lt_iff_exists_real_btwn.mp hy
    obtain ⟨s, hys, hsr⟩ := EReal.lt_iff_exists_real_btwn.mp hyr
    have hsr' : s < r := by exact_mod_cast hsr
    have hr : ∀ γ, r ≤ ϕ ε₀ γ := fun γ => by
      have := (le_iInf_iff.mp hrΦ.le) γ
      exact_mod_cast this
    have hcont : ContinuousAt (fun ε : E => L * ‖ε₀ - ε‖) ε₀ :=
      (continuous_const.mul (continuous_norm.comp (continuous_const.sub continuous_id))).continuousAt
    have hev : ∀ᶠ ε in nhds ε₀, L * ‖ε₀ - ε‖ < r - s := by
      apply hcont.eventually (gt_mem_nhds _)
      simp [sub_pos, hsr']
    filter_upwards [hev] with ε hε
    have hle : (s : EReal) ≤ ⨅ γ, (ϕ ε γ : EReal) := by
      refine le_iInf fun γ => ?_
      have := h ε γ
      have h3 := hr γ
      have : (s : ℝ) ≤ ϕ ε γ := by nlinarith
      exact_mod_cast this
    exact lt_of_lt_of_le hys hle
