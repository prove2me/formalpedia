-- Prove2me | solution 1 for WorkbookCorrected.plus_25163
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-01T07:26:16.070705+00:00
-- url     : https://prove2.me/submissions/746a5613-ac16-44d6-bfb5-71960e0120ba

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum

theorem solution : (16215550374995553724649140826784239545968176044228380026973887068188454273239028608101/9917270859375120893045101020037428693596312932340607412425530338350988976871694848000:ℚ) > (7/5:ℚ) := by
  norm_num
