-- Prove2me | solution 1 for SuperstarExcl.Complementors.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:08:53.105325+00:00
-- url     : https://prove2.me/submissions/b6815219-f36f-4e55-a922-e95c2831df9c

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

open SuperstarExcl.Complementors Set Filter Topology

theorem solution (M : Model) (ϕ g₁ g₂ p₁ p₂ D : ℝ)
    (hg₁ : g₁ = 0 ∨ g₁ = 1) (hg₂ : g₂ = 0 ∨ g₂ = 1)
    (heq : IsEquilibrium M ϕ g₁ g₂ p₁ p₂ D) (hD₀ : 0 < D) (hD₁ : D < 1) :
    p₁ = M.F (mstar M ϕ g₁ g₂ p₁ p₂ D) *
        (1 / M.f (mstar M ϕ g₁ g₂ p₁ p₂ D) -
          M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D)))) ∧
      p₂ = (1 - M.F (mstar M ϕ g₁ g₂ p₁ p₂ D)) *
        (1 / M.f (mstar M ϕ g₁ g₂ p₁ p₂ D) -
          M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D)))) := by
  obtain ⟨hFE, hdev1, hdev2⟩ := heq
  set x := mstar M ϕ g₁ g₂ p₁ p₂ D with hx
  have hFE' : D = M.F x := hFE
  have hxmem : x ∈ Ioo (-M.mbar) M.mbar := by
    constructor
    · by_contra h
      have := M.F_eq_zero x (not_lt.mp h); rw [← hFE'] at this; linarith
    · by_contra h
      have := M.F_eq_one x (not_lt.mp h); rw [← hFE'] at this; linarith
  -- the reduced map `K m = θ (Λ(γ F m) - Λ(γ (1 - F m))) - m`
  let K : ℝ → ℝ := fun m => M.θ * (M.Λ (M.γ * M.F m) - M.Λ (M.γ * (1 - M.F m))) - m
  set κ : ℝ := M.f x * M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D))) - 1 with hκdef
  have hκneg : κ < 0 := by
    have h3 := M.assumption3 x hxmem
    rw [← hFE'] at h3; linarith
  have hfx : 0 < M.f x := M.f_pos x hxmem
  have hFs : HasStrictDerivAt M.F (M.f x) x :=
    (M.F_contDiffOn.contDiffAt (Ioo_mem_nhds hxmem.1 hxmem.2)).hasStrictDerivAt'
      (M.F_hasDerivAt x hxmem) (by norm_num)
  have hΛs : ∀ y, HasStrictDerivAt M.Λ (M.lam y) y := fun y =>
    M.Λ_contDiff.contDiffAt.hasStrictDerivAt' (M.Λ_hasDerivAt y) (by norm_num)
  have hKs : HasStrictDerivAt K κ x := by
    have h1 := (hΛs (M.γ * M.F x)).comp x (hFs.const_mul M.γ)
    have h2 := (hΛs (M.γ * (1 - M.F x))).comp x ((hFs.const_sub 1).const_mul M.γ)
    have := ((h1.sub h2).const_mul M.θ).sub (hasStrictDerivAt_id x)
    refine HasStrictDerivAt.congr_deriv this ?_
    rw [hκdef, hFE']; ring
  have hκ : κ ≠ 0 := hκneg.ne
  set g := HasStrictDerivAt.localInverse K κ x hKs hκ with hgdef
  set y₀ := K x with hy₀
  have hg : HasStrictDerivAt g κ⁻¹ y₀ := hKs.to_localInverse hκ
  have hright : ∀ᶠ y in 𝓝 y₀, K (g y) = y := hKs.eventually_right_inverse hκ
  have hgx : g y₀ = x := (hKs.eventually_left_inverse hκ).self_of_nhds
  -- value of `K x` at the equilibrium
  have hKx : y₀ = p₁ - p₂ - ϕ * (g₁ - g₂) := by
    have : x = ϕ * (g₁ - g₂) - (p₁ - p₂) +
        M.θ * (M.Λ (M.γ * D) - M.Λ (M.γ * (1 - D))) := by
      simp only [hx, mstar, mtilde]
    simp only [hy₀, K]; rw [← hFE']; linarith
  have hFg : HasDerivAt M.F (M.f x) (g y₀) := by rw [hgx]; exact M.F_hasDerivAt x hxmem
  -- FE demand from the local branch
  have hFEbranch : ∀ q₁ q₂ : ℝ, K (g (q₁ - q₂ - ϕ * (g₁ - g₂))) = q₁ - q₂ - ϕ * (g₁ - g₂) →
      IsFEDemand M ϕ g₁ g₂ q₁ q₂ (M.F (g (q₁ - q₂ - ϕ * (g₁ - g₂)))) := by
    intro q₁ q₂ hK
    unfold IsFEDemand
    congr 1
    simp only [mtilde]
    simp only [K] at hK
    linarith
  -- platform 1
  have hmax1 : IsLocalMax (fun s => (p₁ + s) * M.F (g (y₀ + s))) 0 := by
    have hc : Tendsto (fun s : ℝ => y₀ + s) (𝓝 0) (𝓝 y₀) := by
      have := (continuous_const.add continuous_id).tendsto (0:ℝ) (f := fun s : ℝ => y₀ + s)
      simpa using this
    filter_upwards [hc.eventually hright] with s hs
    simp only [add_zero, hgx]
    have e : y₀ + s = (p₁ + s) - p₂ - ϕ * (g₁ - g₂) := by rw [hKx]; ring
    rw [e] at hs ⊢
    have := hdev1 (p₁ + s) _ (hFEbranch _ _ hs)
    rw [hFE'] at this; exact this
  have hπ1 : HasDerivAt (fun s => (p₁ + s) * M.F (g (y₀ + s)))
      (1 * M.F (g (y₀ + 0)) + (p₁ + 0) * (M.f x * (κ⁻¹ * 1))) 0 := by
    have hin : HasDerivAt (fun s : ℝ => y₀ + s) 1 0 := (hasDerivAt_id (0:ℝ)).const_add y₀
    have hg' : HasDerivAt g κ⁻¹ (y₀ + 0) := by rw [add_zero]; exact hg.hasDerivAt
    have hF' : HasDerivAt M.F (M.f x) (g (y₀ + 0)) := by rw [add_zero]; exact hFg
    exact ((hasDerivAt_id (0:ℝ)).const_add p₁).mul (hF'.comp 0 (hg'.comp 0 hin))
  have hz1 := hmax1.hasDerivAt_eq_zero hπ1
  -- platform 2
  have hmax2 : IsLocalMax (fun s => (p₂ + s) * (1 - M.F (g (y₀ - s)))) 0 := by
    have hc : Tendsto (fun s : ℝ => y₀ - s) (𝓝 0) (𝓝 y₀) := by
      have := (continuous_const.sub continuous_id).tendsto (0:ℝ) (f := fun s : ℝ => y₀ - s)
      simpa using this
    filter_upwards [hc.eventually hright] with s hs
    simp only [add_zero, sub_zero, hgx]
    have e : y₀ - s = p₁ - (p₂ + s) - ϕ * (g₁ - g₂) := by rw [hKx]; ring
    rw [e] at hs ⊢
    have := hdev2 (p₂ + s) _ (hFEbranch _ _ hs)
    rw [hFE'] at this; exact this
  have hπ2 : HasDerivAt (fun s => (p₂ + s) * (1 - M.F (g (y₀ - s))))
      (1 * (1 - M.F (g (y₀ - 0))) + (p₂ + 0) * (-(M.f x * (κ⁻¹ * (-1))))) 0 := by
    have hin : HasDerivAt (fun s : ℝ => y₀ - s) (-1) 0 := (hasDerivAt_id (0:ℝ)).const_sub y₀
    have hg' : HasDerivAt g κ⁻¹ (y₀ - 0) := by rw [sub_zero]; exact hg.hasDerivAt
    have hF' : HasDerivAt M.F (M.f x) (g (y₀ - 0)) := by rw [sub_zero]; exact hFg
    exact ((hasDerivAt_id (0:ℝ)).const_add p₂).mul ((hF'.comp 0 (hg'.comp 0 hin)).const_sub 1)
  have hz2 := hmax2.hasDerivAt_eq_zero hπ2
  rw [add_zero, hgx, add_zero] at hz1
  rw [sub_zero, hgx, add_zero] at hz2
  rw [← hFE'] at hz1 hz2 ⊢
  have hκv : κ = M.f x * (M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D)))) - 1 := by
    rw [hκdef]; ring
  constructor
  · have h : (1 * D + p₁ * (M.f x * (κ⁻¹ * 1))) * κ = 0 := by rw [hz1]; ring
    field_simp at h
    rw [hκv] at h
    generalize M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D))) = L at h ⊢
    field_simp
    linarith
  · have h : (1 * (1 - D) + p₂ * (-(M.f x * (κ⁻¹ * (-1))))) * κ = 0 := by rw [hz2]; ring
    field_simp at h
    rw [hκv] at h
    generalize M.γ * M.θ * (M.lam (M.γ * D) + M.lam (M.γ * (1 - D))) = L at h ⊢
    field_simp
    linarith
