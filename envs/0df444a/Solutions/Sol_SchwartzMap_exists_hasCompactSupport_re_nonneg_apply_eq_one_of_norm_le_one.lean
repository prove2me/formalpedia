-- Prove2me | solution 1 for SchwartzMap.exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/3555a871-39f0-5eaa-8dd0-022a13c04477

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one

set_option autoImplicit false

open scoped SchwartzMap

namespace ArchBump

theorem main (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, zero_lt_one, one_lt_two⟩
  let f : E → ℂ := fun x => ((b x : ℝ) : ℂ)
  have hfc : HasCompactSupport f := b.hasCompactSupport.comp_left Complex.ofReal_zero
  have hfs : ContDiff ℝ (⊤ : ℕ∞) f := (Complex.ofRealCLM.contDiff.of_le le_top).comp b.contDiff
  have happ : ∀ x, hfc.toSchwartzMap hfs x = f x := fun _ => rfl
  refine ⟨hfc.toSchwartzMap hfs, ?_, ?_, ?_, ?_, ?_⟩
  · have hco : ((hfc.toSchwartzMap hfs : 𝓢(E, ℂ)) : E → ℂ) = f := funext happ
    rw [hco]; exact hfc
  · intro x
    rw [happ]
    exact ⟨by simpa [f] using b.nonneg, by simp [f]⟩
  · intro x
    rw [happ]
    simp only [f, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg b.nonneg]
    exact b.le_one
  · intro x hx
    rw [happ]
    simp only [f, Complex.ofReal_eq_one]
    exact b.one_of_mem_closedBall (by simpa using hx)
  · intro x hx
    rw [happ]
    simp only [f, Complex.ofReal_eq_zero]
    exact b.zero_of_le_dist (by simpa using hx)

end ArchBump

theorem solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ g : 𝓢(E, ℂ), HasCompactSupport g ∧ (∀ x, 0 ≤ (g x).re ∧ (g x).im = 0) ∧ (∀ x, ‖g x‖ ≤ 1) ∧
      (∀ x, ‖x‖ ≤ 1 → g x = 1) ∧ (∀ x, 2 ≤ ‖x‖ → g x = 0) :=
  ArchBump.main E

end S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one
end P2MW
export P2MW.S_SchwartzMap_exists_hasCompactSupport_re_nonneg_apply_eq_one_of_norm_le_one (solution)
