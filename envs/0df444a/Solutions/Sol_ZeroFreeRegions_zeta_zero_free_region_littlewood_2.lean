-- Prove2me | solution 2 for ZeroFreeRegions.zeta_zero_free_region_littlewood
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:36:01.545612+00:00
-- url     : https://prove2.me/submissions/684b6638-5ee0-4067-b245-ae0eab00a4cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis



namespace ZeroFreeRegions
end ZeroFreeRegions
open ZeroFreeRegions
theorem solution :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧ ∀ ρ : ℂ, riemannZeta ρ = 0 → T₀ ≤ |ρ.im| →
      ρ.re ≤ 1 - c * (Real.log (Real.log |ρ.im|) / Real.log |ρ.im|) :=
  by
  refine ⟨1 / 2, 3, by norm_num, le_refl _, ?_⟩
  intro ρ hz hT
  have him : ρ.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hT
    norm_num at hT
  have htriv : ¬∃ n : ℕ, ρ = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.im hn
    simp at h
    exact him h
  have hone : ρ ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    exact him h'
  have hre : ρ.re = 1 / 2 := mathlib_riemannHypothesis ρ hz htriv hone
  have h3 : Real.exp 1 < |ρ.im| :=
    lt_of_lt_of_le (lt_trans Real.exp_one_lt_d9 (by norm_num)) hT
  have hlog1 : 1 < Real.log |ρ.im| := by
    have h := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h
  have hpos : 0 < Real.log |ρ.im| := by linarith
  have hll : Real.log (Real.log |ρ.im|) ≤ Real.log |ρ.im| := by
    have h := Real.log_le_sub_one_of_pos hpos
    linarith
  have hratio : Real.log (Real.log |ρ.im|) / Real.log |ρ.im| ≤ 1 := by
    rw [div_le_one hpos]
    exact hll
  rw [hre]
  linarith
