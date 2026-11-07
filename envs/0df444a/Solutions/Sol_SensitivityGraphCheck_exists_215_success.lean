-- Prove2me | solution 1 for SensitivityGraphCheck.exists_215_success
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-11-06T18:59:12.096682+00:00
-- url     : https://prove2.me/submissions/9b6f08e0-d9c3-4fb2-9938-27bb1f4da76f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityGraphLocal_succeeds_eq
import Theorems.Thm_SensitivityGraphLocal_exists_215_success

set_option autoImplicit false

theorem solution :
    ∃ (D : SensitivityGraphCheck.RawData) (n k : ℕ),
      SensitivityGraphCheck.succeeds D (n + 1) k = true := by
  obtain ⟨D, n, k, h⟩ := SensitivityGraphLocal.exists_215_success
  exact ⟨D, n, k, (SensitivityGraphLocal.succeeds_eq D (n + 1) k).symm.trans h⟩
