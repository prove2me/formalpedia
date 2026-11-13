-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.ising_rsb_threshold
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T05:13:57.502011+00:00
-- url     : https://prove2.me/submissions/53416655-979f-4a3e-8a0c-d0cce91d3839
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_lower_bound
import Theorems.Thm_ZeroFreeRRG_Hardcore_ising_rsb_upper_bound
open ZeroFreeRRG.Hardcore

theorem solution (d : ℕ) (hd : 3 ≤ d) :
    betaRSB d 2 = (Real.sqrt ((d : ℝ) - 1) - 1) / (Real.sqrt ((d : ℝ) - 1) + 1) :=
  le_antisymm (ising_rsb_upper_bound d hd) (ising_rsb_lower_bound d hd)
