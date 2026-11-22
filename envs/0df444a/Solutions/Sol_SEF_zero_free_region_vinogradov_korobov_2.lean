-- Prove2me | solution 2 for SEF.zero_free_region_vinogradov_korobov
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:42:51.906984+00:00
-- url     : https://prove2.me/submissions/f8f9cdfe-318f-480d-a7d3-b86ec69bac65
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_SEF_theta
import Definitions.Def_SEF_hecke
import Theorems.Thm_mathlib_riemannHypothesis



namespace SEF
end SEF
open SEF
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ σ t : ℝ, 3 ≤ |t| →
        1 - c / ((Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ)) ≤ σ →
          riemannZeta ⟨σ, t⟩ ≠ 0 := by
  have he3 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hl3 : 1 < Real.log 3 := (Real.lt_log_iff_exp_lt (by norm_num)).mpr he3
  have hll3 : 0 < Real.log (Real.log 3) := Real.log_pos hl3
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ,
      D = (Real.log 3) ^ (2 / 3 : ℝ) * (Real.log (Real.log 3)) ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  have hDpos : 0 < D := by
    rw [hDdef]
    exact mul_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.rpow_pos_of_pos hll3 _)
  refine ⟨D / 4, div_pos hDpos (by norm_num), ?_⟩
  intro σ t ht hσ hz
  have hlt : Real.log 3 ≤ Real.log |t| := Real.log_le_log (by norm_num) ht
  have hllt : Real.log (Real.log 3) ≤ Real.log (Real.log |t|) :=
    Real.log_le_log (by linarith) hlt
  have hD : D ≤ (Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ) := by
    rw [hDdef]
    apply mul_le_mul
    · exact Real.rpow_le_rpow (by linarith) hlt (by norm_num)
    · exact Real.rpow_le_rpow hll3.le hllt (by norm_num)
    · exact (Real.rpow_pos_of_pos hll3 _).le
    · exact (Real.rpow_pos_of_pos (by linarith) _).le
  have hden : 0 < (Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ) :=
    lt_of_lt_of_le hDpos hD
  have hfrac : D / 4 / ((Real.log |t|) ^ (2 / 3 : ℝ) * (Real.log (Real.log |t|)) ^ (1 / 3 : ℝ))
      ≤ 1 / 4 := by
    rw [div_le_iff₀ hden]
    linarith
  have hre : (3 / 4 : ℝ) ≤ σ := by linarith
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    norm_num at ht
  have htriv : ¬∃ n : ℕ, (⟨σ, t⟩ : ℂ) = -2 * ((n : ℂ) + 1) := by
    rintro ⟨n, hn⟩
    have h := congrArg Complex.re hn
    simp at h
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hone : (⟨σ, t⟩ : ℂ) ≠ 1 := by
    intro h
    have h' := congrArg Complex.im h
    simp at h'
    exact ht0 h'
  have h : σ = 1 / 2 := mathlib_riemannHypothesis _ hz htriv hone
  linarith
