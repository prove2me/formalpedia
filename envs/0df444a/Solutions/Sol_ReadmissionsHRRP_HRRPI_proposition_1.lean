-- Prove2me | solution 1 for ReadmissionsHRRP.HRRPI.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T19:47:04.604661+00:00
-- url     : https://prove2.me/submissions/a3bd702e-7cd9-4895-bc30-37530858e391

import Mathlib
import Definitions.Def_ReadmissionsHRRP_HRRPI_Setting
import Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_existence
import Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_ordering
import Theorems.Thm_ReadmissionsHRRP_HRRPI_proposition_1_two_hospitals

open ReadmissionsHRRP.HRRPI

theorem solution (M : Model) (hM : M.Standing) (hA : M.FirstBestInterior)
    (N : ℕ) (hN : 2 ≤ N) :
    (∃ p : ℝ × ℝ, M.IsSymEqI N p) ∧
    (∀ p : ℝ × ℝ, M.IsSymEqI N p →
      ∀ xs : ℝ × ℝ, M.IsFirstBest xs → p.1 < xs.1 ∧ xs.2 < p.2) ∧
    (∀ x : Fin 2 → ℝ × ℝ, M.IsEqI 2 x → x 0 = x 1) :=
  ⟨proposition_1_existence M hM hA N hN, proposition_1_ordering M hM hA N hN,
    proposition_1_two_hospitals M hM hA⟩
