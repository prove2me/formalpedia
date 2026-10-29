-- Prove2me | solution 2 for SensitivityProfileCycle.exists_215_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dmilosch
-- created : 2026-10-28T23:52:53.952727+00:00
-- url     : https://prove2.me/submissions/d66915bf-ca17-461c-9524-9887dd3a2ba7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_SensitivityVariableWord_certificate_iff_word
import Theorems.Thm_SensitivityVariableWord_exists_215_word

set_option autoImplicit false

theorem solution :
    ∃ c : SensitivityProfileCycle.Certificate,
      1 < c.radius ∧ c.radius ^ 43 < (c.vertices ^ c.period) ^ 20 := by
  exact SensitivityVariableWord.certificate_iff_word.mpr
    SensitivityVariableWord.exists_215_word
