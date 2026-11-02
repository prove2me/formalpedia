-- Prove2me | solution 1 for TiltingFTT.Optimal.welfare_improving_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:45:52.443706+00:00
-- url     : https://prove2.me/submissions/b810379b-3c69-4766-bee3-e2369d743a55

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal

theorem solution :
    ∃ (P : Firm) (VH VL v : ℝ), Standing P ∧ Spec23 P VH VL v ∧ 0 < v ∧ Coexist P 0 ∧
      tauStar P < tau0 P v ∧ 0 < tauStar P ∧ poolWelfare P 0 1 < WS P (tauStar P) := by
  refine ⟨⟨1/2, 8/5, 1, 23, 13, 20, 10, 17, 7⟩, 20, 10, 3, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · unfold Standing; norm_num
  · unfold Spec23; norm_num
  · unfold Coexist Cond17 Fbar; norm_num
  · unfold tauStar tau0 Fbar; norm_num
  · unfold tauStar Fbar; norm_num
  · unfold poolWelfare WS Tbar tauStar welfare Wstar Fbar; norm_num
