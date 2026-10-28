-- Prove2me | solution 1 for OAI.common_bases_fpras
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T00:27:01.626026+00:00
-- url     : https://prove2.me/submissions/c986b547-faf7-4b24-a9a3-a608e5cdf8da
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CountingMatroid_Bridge_mainTheorem_of_explicit_machine_realization
import Theorems.Thm_CountingMatroid_Bridge_explicit_machine_realization

theorem solution : OAI.CommonBasesFPRAS.MainTheorem :=
  CountingMatroid.Bridge.mainTheorem_of_explicit_machine_realization
    CountingMatroid.Bridge.explicit_machine_realization
