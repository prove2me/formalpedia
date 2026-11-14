-- Prove2me | solution 3 for SensitivityProfileCycle.exists_215_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ng Xuan Hern
-- created : 2026-11-14T01:40:39.99655+00:00
-- url     : https://prove2.me/submissions/2c25bac2-351b-4d2f-b14d-efba835e79da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityVariableWord_certificate_iff_word
import Theorems.Thm_SensitivityVariableWord_exists_215_word

theorem solution :
    ∃ c : SensitivityProfileCycle.Certificate,
      1 < c.radius ∧ c.radius ^ 43 < (c.vertices ^ c.period) ^ 20 := by
  exact SensitivityVariableWord.certificate_iff_word.mpr
    SensitivityVariableWord.exists_215_word
