-- Prove2me | solution 1 for TongString.exists_modularAction_mem_fundamental_domain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T18:01:58.991243+00:00
-- url     : https://prove2.me/submissions/8ca5e340-dc6e-4e26-8964-4e4f246aef43

import Mathlib
import Definitions.Def_TongString_modular_action

open TongString in
theorem solution (τ : ℂ) (hτ : 0 < τ.im) :
    ∃ a b c d : ℤ, a * d - b * c = 1 ∧
      1 ≤ ‖modularAction a b c d τ‖ ∧ |(modularAction a b c d τ).re| ≤ 1 / 2 := by
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd (⟨τ, hτ⟩ : UpperHalfPlane)
  have hmem : ((g • (⟨τ, hτ⟩ : UpperHalfPlane) : UpperHalfPlane) : ℂ) ∈ (↑) '' ModularGroup.fd := ⟨_, hg, rfl⟩
  rw [ModularGroup.coe_fd] at hmem
  have hcoe := UpperHalfPlane.coe_specialLinearGroup_apply g (⟨τ, hτ⟩ : UpperHalfPlane)
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rw [Matrix.det_fin_two] at this
    exact this
  refine ⟨g 0 0, g 0 1, g 1 0, g 1 1, hdet, ?_, ?_⟩
  · have h := hmem.2.1
    rw [hcoe] at h
    simpa [TongString.modularAction] using h
  · have h := hmem.2.2
    rw [hcoe] at h
    simpa [TongString.modularAction] using h
