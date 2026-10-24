-- Prove2me | solution 1 for SuperstarExcl.Complementors.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T00:06:37.737654+00:00
-- url     : https://prove2.me/submissions/590e8a0c-03ec-4923-83b7-28c55ed884e9

import Mathlib
import Definitions.Def_SuperstarExcl_Complementors_Model
import Definitions.Def_SuperstarExcl_Complementors_Market

open SuperstarExcl.Complementors Set Filter Topology

theorem solution (M : Model) (ϕ p D : ℝ)
    (heq : IsEquilibrium M ϕ 1 1 p p D) (hD₀ : 0 < D) (hD₁ : D < 1) :
    p = 1 / (2 * M.f 0) - M.γ * M.θ * M.lam (M.γ / 2) ∧
      mstar M ϕ 1 1 p p D = 0 ∧ D = 1 / 2 ∧
      M.Λ (M.γ * D) = M.Λ (M.γ / 2) ∧ M.Λ (M.γ * (1 - D)) = M.Λ (M.γ / 2) ∧
      (∀ k, (Joins M D k ∨ Joins M (1 - D) k) → Multihomes M D (1 - D) k) ∧
      (∀ k, M.γ / 2 < k → Zerohomes M D (1 - D) k) := by
  obtain ⟨hFE, hdev1, -⟩ := heq
  have hF0 : M.F 0 = 1 / 2 := by have := M.F_symm 0; simp at this; linarith
  have hmem0 : (0:ℝ) ∈ Ioo (-M.mbar) M.mbar := ⟨by linarith [M.mbar_pos], M.mbar_pos⟩
  -- the reduced map `K m = θ (Λ(γ F m) - Λ(γ (1 - F m))) - m`
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
    · intro x hx; exact (hKderiv x hx).continuousAt.continuousWithinAt
    · intro x hx
      rw [interior_Ioo] at hx
      rw [(hKderiv x hx).deriv]; exact hKneg x hx
  -- the fulfilled-expectations condition
  set x := mtilde M ϕ 1 1 p p (M.Λ (M.γ * D)) (M.Λ (M.γ * (1 - D))) with hx
  have hxv : x = M.θ * (M.Λ (M.γ * D) - M.Λ (M.γ * (1 - D))) := by
    simp only [hx, mtilde]; ring
  have hFE' : D = M.F x := hFE
  have hxmem : x ∈ Ioo (-M.mbar) M.mbar := by
    constructor
    · by_contra h
      push_neg at h
      have := M.F_eq_zero x h; rw [← hFE'] at this; linarith
    · by_contra h
      push_neg at h
      have := M.F_eq_one x h; rw [← hFE'] at this; linarith
  have hKx : K x = 0 := by
    simp only [K]; rw [← hFE', hxv]; ring
  have hK0 : K 0 = 0 := by
    simp only [K]; rw [hF0]; norm_num
  have hx0 : x = 0 := hKanti.injOn hxmem hmem0 (by rw [hKx, hK0])
  have hDhalf : D = 1 / 2 := by rw [hFE', hx0, hF0]
  -- strict differentiability of K at 0
  have hFs : HasStrictDerivAt M.F (M.f 0) 0 :=
    (M.F_contDiffOn.contDiffAt (Ioo_mem_nhds hmem0.1 hmem0.2)).hasStrictDerivAt'
      (M.F_hasDerivAt 0 hmem0) (by norm_num)
  have hΛs : ∀ y, HasStrictDerivAt M.Λ (M.lam y) y := fun y =>
    M.Λ_contDiff.contDiffAt.hasStrictDerivAt' (M.Λ_hasDerivAt y) (by norm_num)
  have hKs : HasStrictDerivAt K (K' 0) 0 := by
    have h1 := (hΛs (M.γ * M.F 0)).comp 0 (hFs.const_mul M.γ)
    have h2 := (hΛs (M.γ * (1 - M.F 0))).comp 0 ((hFs.const_sub 1).const_mul M.γ)
    have := ((h1.sub h2).const_mul M.θ).sub (hasStrictDerivAt_id 0)
    refine HasStrictDerivAt.congr_deriv this ?_
    simp only [K']
  have hκ : K' 0 ≠ 0 := (hKneg 0 hmem0).ne
  set g := HasStrictDerivAt.localInverse K (K' 0) 0 hKs hκ with hgdef
  have hg : HasStrictDerivAt g (K' 0)⁻¹ (K 0) := hKs.to_localInverse hκ
  rw [hK0] at hg
  have hright : ∀ᶠ s in 𝓝 (K 0), K (g s) = s := hKs.eventually_right_inverse hκ
  rw [hK0] at hright
  have hg0 : g 0 = 0 := by
    have := (hKs.eventually_left_inverse hκ).self_of_nhds
    rw [hK0] at this; exact this
  -- the profit of platform 1 along the local branch of FE demand
  have hlocmax : IsLocalMax (fun s => (p + s) * M.F (g s)) 0 := by
    filter_upwards [hright] with s hs
    simp only [add_zero, hg0, hF0]
    have hfe : IsFEDemand M ϕ 1 1 (p + s) p (M.F (g s)) := by
      unfold IsFEDemand
      congr 1
      simp only [mtilde] at hs ⊢
      simp only [K] at hs
      linarith
    have := hdev1 (p + s) (M.F (g s)) hfe
    rw [hDhalf] at this; exact this
  have hFg : HasDerivAt M.F (M.f 0) (g 0) := by rw [hg0]; exact M.F_hasDerivAt 0 hmem0
  have hπ : HasDerivAt (fun s => (p + s) * M.F (g s))
      (1 * M.F (g 0) + (p + 0) * (M.f 0 * (K' 0)⁻¹)) 0 := by
    have := ((hasDerivAt_id (0:ℝ)).const_add p).mul (hFg.comp 0 hg.hasDerivAt)
    refine HasDerivAt.congr_deriv this ?_
    simp
  have hzero := hlocmax.hasDerivAt_eq_zero hπ
  rw [hg0, hF0, add_zero] at hzero
  have hκv : K' 0 = 2 * M.θ * M.γ * M.f 0 * M.lam (M.γ / 2) - 1 := by
    simp only [K']; rw [hF0]
    rw [show M.γ * (1 / 2) = M.γ / 2 by ring, show M.γ * (1 - 1 / 2) = M.γ / 2 by ring]; ring
  have hf0 : 0 < M.f 0 := M.f_pos 0 hmem0
  have hpf : p * M.f 0 = - K' 0 / 2 := by
    have : (1 * (1 / 2) + p * (M.f 0 * (K' 0)⁻¹)) * K' 0 = 0 := by rw [hzero]; ring
    field_simp at this
    linarith
  refine ⟨?_, ?_, hDhalf, ?_, ?_, ?_, ?_⟩
  · rw [hκv] at hpf
    field_simp
    nlinarith
  · show x = 0; exact hx0
  · rw [hDhalf]; ring_nf
  · rw [hDhalf]; ring_nf
  · intro k hk
    simp only [Multihomes, Joins] at hk ⊢
    rw [hDhalf] at hk ⊢
    have e : (1:ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [e] at hk ⊢
    rcases hk with h | h <;> exact ⟨h, h⟩
  · intro k hk
    simp only [Zerohomes, Joins]
    rw [hDhalf]
    constructor <;> intro h <;> linarith
