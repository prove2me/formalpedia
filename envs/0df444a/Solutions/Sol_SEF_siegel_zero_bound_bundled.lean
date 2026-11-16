-- Prove2me | solution 1 for SEF.siegel_zero_bound_bundled
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T22:13:25.258652+00:00
-- url     : https://prove2.me/submissions/901f931e-b0b1-41f5-99a2-34fd1b98d940

import Mathlib
import Theorems.Thm_TowardsGRH_LW56e2_b83dbbd_dirichlet_zero_free_bound

theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q], 3 ≤ q →
      ∀ χ : DirichletCharacter ℂ q,
        χ.IsPrimitive → χ ≠ 1 → (∀ a : ZMod q, (χ a).im = 0) →
        ∀ β : ℝ,
          (0 < β ∧ β < 1 ∧ DirichletCharacter.LFunction χ (β : ℂ) = 0) →
          c ≤ (1 - β) * Real.log (q : ℝ) := by
  refine ⟨1 / 8, by norm_num, ?_⟩
  rintro q _ hq χ - - - β ⟨-, hβ1, hz⟩
  -- the zero cannot lie in the zero-free half-plane
  have hβ : β ≤ 0.8749570698 := by
    by_contra h
    push_neg at h
    refine TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound χ (s := (β : ℂ))
      (by simpa using h) ?_ hz
    rintro ⟨-, h1⟩
    have : β = 1 := by exact_mod_cast h1
    linarith
  -- log q ≥ log 3 ≥ 1
  have hlog : 1 ≤ Real.log (q : ℝ) := by
    have h3 : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have he : Real.exp 1 ≤ (q : ℝ) := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (q : ℝ) := Real.log_le_log (Real.exp_pos 1) he
  nlinarith
