-- Prove2me | solution 1 for Plasticity.SeqSpace.le_c0_of_bijOn_ballIn
-- status  : ACCEPTED   (prove)
-- author  : @scanstone
-- created : 2026-10-15T08:08:21.212772+00:00
-- url     : https://prove2.me/submissions/a5c7d9d9-d712-4e7b-81ce-c3509f95be61

import Definitions.Def_Plasticity_SeqSpace
import Mathlib.Topology.EMetricSpace.Lipschitz
import Theorems.Thm_Plasticity_SeqSpace_exists_signed_permutation_inward

open Filter Topology Plasticity

namespace Sol_Plasticity_SeqSpace_le_c0_of_bijOn_ballIn

/-- The normal form bounds every output coordinate by the matching input coordinate. -/
theorem abs_le_of_inward {a u v : ℝ} (ha : a = 1 ∨ a = -1)
    (h : (0 ≤ u → 0 ≤ a * v ∧ a * v ≤ u) ∧ (u ≤ 0 → u ≤ a * v ∧ a * v ≤ 0)) : |v| ≤ |u| := by
  have hav : |a * v| = |v| := by
    rcases ha with rfl | rfl <;> simp
  rw [← hav]
  rcases le_total 0 u with hu | hu
  · obtain ⟨h1, h2⟩ := h.1 hu
    rw [abs_of_nonneg h1, abs_of_nonneg hu]; exact h2
  · obtain ⟨h1, h2⟩ := h.2 hu
    rw [abs_of_nonpos h2, abs_of_nonpos hu]; linarith

end Sol_Plasticity_SeqSpace_le_c0_of_bijOn_ballIn

theorem solution {Γ Δ : Type*} (X : Submodule ℝ (Linf Γ)) (Y : Submodule ℝ (Linf Δ))
    (hX0 : c00 Γ ≤ X) (hX1 : X ≤ c0 Γ) (hY0 : c00 Δ ≤ Y)
    (F : Linf Γ → Linf Δ)
    (hbij : Set.BijOn F (ballIn X) (ballIn Y))
    (hlip : LipschitzOnWith 1 F (ballIn X)) :
    Y ≤ c0 Δ := by
  obtain ⟨σ, α, hα, hF⟩ :=
    Plasticity.SeqSpace.exists_signed_permutation_inward X Y hX0 hX1 hY0 F hbij hlip
  -- every image of the ball vanishes at infinity, because `|F x (σ n)| ≤ |x n|`
  have himg : ∀ x ∈ ballIn X, F x ∈ c0 Δ := by
    intro x hx
    have hxc : Tendsto (⇑x) cofinite (𝓝 0) := hX1 hx.1
    have h1 : Tendsto (fun n => F x (σ n)) cofinite (𝓝 0) :=
      squeeze_zero_norm
        (fun n => Sol_Plasticity_SeqSpace_le_c0_of_bijOn_ballIn.abs_le_of_inward (hα n) (hF x hx n))
        (by simpa using hxc.norm)
    have h2 := h1.comp σ.symm.injective.tendsto_cofinite
    show Tendsto (⇑(F x)) cofinite (𝓝 0)
    simpa [Function.comp_def] using h2
  -- the ball of `Y` is the image of the ball of `X`, and `Y` is spanned by its ball
  intro y hy
  by_cases hy0 : y = 0
  · rw [hy0]; exact (c0 Δ).zero_mem
  have hpos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hyB : ‖y‖⁻¹ • y ∈ ballIn Y := by
    refine ⟨Y.smul_mem _ hy, ?_⟩
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
  obtain ⟨x, hx, hFx⟩ := hbij.surjOn hyB
  have hc := (c0 Δ).smul_mem ‖y‖ (hFx ▸ himg x hx)
  rwa [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul] at hc
