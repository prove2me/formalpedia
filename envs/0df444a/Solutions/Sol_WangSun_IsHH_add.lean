-- Prove2me | solution 1 for WangSun.IsHH_add
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T12:39:46.536467+00:00
-- url     : https://prove2.me/submissions/3994a934-08bf-43e5-8021-0fc143e08b78

import Definitions.Def_WangSunCPWL

open Finset

variable {n : ℕ}

theorem solution {f g : (Fin n → ℝ) → ℝ} (hf : IsHH f) (hg : IsHH g) : IsHH (f + g) := by
  obtain ⟨K1, h1, hh1, rfl⟩ := hf
  obtain ⟨K2, h2, hh2, rfl⟩ := hg
  refine ⟨K1 + K2, Fin.append h1 h2, ?_, ?_⟩
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · rw [Fin.append_left]; exact hh1 i
    · rw [Fin.append_right]; exact hh2 i
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
