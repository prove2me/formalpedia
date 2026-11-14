-- Prove2me | solution 1 for SensitivityGraphLocal.exists_215_success
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leedayshaun
-- created : 2026-11-13T20:09:11.567626+00:00
-- url     : https://prove2.me/submissions/5f9fe40a-8a26-4a12-a0ef-a677391cc425
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_SensitivityGraphLocal
import Theorems.Thm_SensitivityGraphLocal_succeeds_eq
import Theorems.Thm_SensitivityGraphCheck_exists_215_success

theorem solution :
    ∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphLocal.succeeds D (n + 1) k = true := by
  rcases SensitivityGraphCheck.exists_215_success with ⟨D, n, k, h⟩
  refine ⟨D, n, k, ?_⟩
  rw [SensitivityGraphLocal.succeeds_eq]
  exact h
