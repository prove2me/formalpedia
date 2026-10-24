-- Prove2me | solution 1 for SuperstarExcl.Complementors.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:10:13.848996+00:00
-- url     : https://prove2.me/submissions/4173027d-b528-4384-a607-cd0c1fea403c

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market
import Theorems.Thm_SuperstarExcl_Complementors_lemma_1

open SuperstarExcl.Complementors Set Filter Topology

theorem solution (M : Model) (ϕ : ℝ) (hϕ : 0 < ϕ) (p₁ p₂ D : ℝ → ℝ)
    (hpath : IsExclusivePath M ϕ p₁ p₂ D) :
    1 - D ϕ < D ϕ ∧ M.Λ (M.γ * (1 - D ϕ)) < M.Λ (M.γ * D ϕ) := by
  have hmem : ϕ ∈ Icc (0:ℝ) ϕ := ⟨hϕ.le, le_rfl⟩
  obtain ⟨heq, hD₀, hD₁⟩ := hpath.2.2.2.1 ϕ hmem
  have hγ := M.γ_pos
  have hθ := M.θ_pos
  -- Λ is strictly increasing on [0, γ]
  have hΛmono : StrictMonoOn M.Λ (Icc 0 M.γ) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · exact M.Λ_contDiff.continuous.continuousOn
    · intro k hk
      rw [interior_Icc] at hk
      rw [(M.Λ_hasDerivAt k).deriv]
      exact M.lam_pos k (Ioo_subset_Icc_self hk)
  -- the first-order conditions (Lemma 1)
  have hfoc := lemma_1 M ϕ 1 0 (p₁ ϕ) (p₂ ϕ) (D ϕ) (Or.inr rfl) (Or.inl rfl) heq hD₀ hD₁
  set d := D ϕ with hd
  set x := mstar M ϕ 1 0 (p₁ ϕ) (p₂ ϕ) d with hx
  have hFE' : d = M.F x := heq.1
  have hxmem : x ∈ Ioo (-M.mbar) M.mbar := by
    constructor
    · by_contra h
      have := M.F_eq_zero x (not_lt.mp h); rw [← hFE'] at this; linarith
    · by_contra h
      have := M.F_eq_one x (not_lt.mp h); rw [← hFE'] at this; linarith
  have hmem0 : (0:ℝ) ∈ Ioo (-M.mbar) M.mbar := ⟨by linarith [M.mbar_pos], M.mbar_pos⟩
  have hF0 : M.F 0 = 1 / 2 := by have := M.F_symm 0; simp at this; linarith
  have hfx : 0 < M.f x := M.f_pos x hxmem
  -- the markup factor is positive (Assumption 3)
  have hΦ : 0 < 1 / M.f x - M.γ * M.θ * (M.lam (M.γ * d) + M.lam (M.γ * (1 - d))) := by
    have h3 := M.assumption3 x hxmem
    rw [← hFE'] at h3
    rw [sub_pos, lt_div_iff₀ hfx]; linarith
  have hdiff : p₁ ϕ - p₂ ϕ =
      (2 * d - 1) * (1 / M.f x - M.γ * M.θ * (M.lam (M.γ * d) + M.lam (M.γ * (1 - d)))) := by
    rw [hfoc.1, hfoc.2, ← hFE']; ring
  -- F strictly increasing on the support
  have hFmono : StrictMonoOn M.F (Ioo (-M.mbar) M.mbar) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo _ _)
    · intro y hy; exact (M.F_hasDerivAt y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(M.F_hasDerivAt y hy).deriv]; exact M.f_pos y hy
  -- reduced map K, strictly decreasing by Assumption 3
  let K : ℝ → ℝ := fun m => M.θ * (M.Λ (M.γ * M.F m) - M.Λ (M.γ * (1 - M.F m))) - m
  let K' : ℝ → ℝ := fun m =>
    M.θ * (M.lam (M.γ * M.F m) * (M.γ * M.f m) - M.lam (M.γ * (1 - M.F m)) * (M.γ * -M.f m)) - 1
  have hKderiv : ∀ m ∈ Ioo (-M.mbar) M.mbar, HasDerivAt K (K' m) m := by
    intro m hm
    have hF := M.F_hasDerivAt m hm
    have h1 := (M.Λ_hasDerivAt (M.γ * M.F m)).comp m (hF.const_mul M.γ)
    have h2 := (M.Λ_hasDerivAt (M.γ * (1 - M.F m))).comp m ((hF.const_sub 1).const_mul M.γ)
    exact ((h1.sub h2).const_mul M.θ).sub (hasDerivAt_id m)
  have hKneg : ∀ m ∈ Ioo (-M.mbar) M.mbar, K' m < 0 := by
    intro m hm
    have h3 := M.assumption3 m hm
    have : K' m = M.f m * M.γ * M.θ * (M.lam (M.γ * M.F m) + M.lam (M.γ * (1 - M.F m))) - 1 := by
      simp only [K']; ring
    rw [this]; linarith
  have hKanti : StrictAntiOn K (Ioo (-M.mbar) M.mbar) := by
    apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
    · intro y hy; exact (hKderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Ioo] at hy
      rw [(hKderiv y hy).deriv]; exact hKneg y hy
  have hK0 : K 0 = 0 := by
    simp only [K]; rw [hF0]; norm_num
  have hKx : K x = p₁ ϕ - p₂ ϕ - ϕ := by
    have : x = ϕ * (1 - 0) - (p₁ ϕ - p₂ ϕ) +
        M.θ * (M.Λ (M.γ * d) - M.Λ (M.γ * (1 - d))) := by
      simp only [hx, mstar, mtilde]
    simp only [K]; rw [← hFE']; linarith
  have hhalf : 1 / 2 < d := by
    by_contra hle
    push Not at hle
    -- then the indifferent consumer is at or left of 0
    have hx0 : x ≤ 0 := by
      by_contra hpos
      push Not at hpos
      have := hFmono hmem0 hxmem hpos
      rw [hF0, ← hFE'] at this; linarith
    have hK : K 0 ≤ K x := hKanti.antitoneOn hxmem hmem0 hx0
    rw [hK0, hKx] at hK
    have : (2 * d - 1) * (1 / M.f x - M.γ * M.θ * (M.lam (M.γ * d) + M.lam (M.γ * (1 - d)))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hΦ.le
    linarith
  refine ⟨by linarith, ?_⟩
  apply hΛmono ⟨by nlinarith, by nlinarith⟩ ⟨by nlinarith, by nlinarith⟩
  nlinarith
