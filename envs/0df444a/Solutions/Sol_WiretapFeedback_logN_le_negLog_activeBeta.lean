-- Prove2me | solution 1 for WiretapFeedback.logN_le_negLog_activeBeta
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-02T05:52:37.608824+00:00
-- url     : https://prove2.me/submissions/53af5c0b-cba9-485d-b970-836290b7047f

import Mathlib
import Definitions.Def_WiretapFeedback_negLog2
import Definitions.Def_WiretapFeedback_activeBeta
import Definitions.Def_WiretapFeedback_IsWiretapCode
import Theorems.Thm_WiretapFeedback_logN_le_negLog_beta_codeLaws
import Theorems.Thm_WiretapFeedback_negLog_beta_codeLaws_le_negLog_activeBeta

theorem solution {X Y Z : Type} [Fintype Y] [Fintype Z] {N n : ℕ} [NeZero N]
    (W V : WildeQIT.Channel X (Y × Z)) (V₂ : WildeQIT.Channel X Z) (V₁ : WildeQIT.Channel Z Y)
    (hV : ∀ x y z, (V x).prob (y, z) = (V₂ x).prob z * (V₁ z).prob y)
    (ε δ η : ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hεδ : ε + δ < 1)
    (c : WiretapFeedback.WiretapCode X Y N n) (hc : WiretapFeedback.IsWiretapCode W c ε δ)
    (hη0 : 0 < η) (hη1 : η < 1 - ε - δ) :
    ((Real.logb 2 N : ℝ) : EReal) ≤
      WiretapFeedback.negLog2 (WiretapFeedback.activeBeta (ε + δ + η) W V n) +
        ((2 * Real.logb 2 (1 / η) : ℝ) : EReal) := by
  have h1 := WiretapFeedback.logN_le_negLog_beta_codeLaws W V V₂ V₁ hV ε δ η hε hδ hεδ c hc hη0 hη1
  have h2 := WiretapFeedback.negLog_beta_codeLaws_le_negLog_activeBeta c
    (PMF.uniformOfFintype (Fin N)) W V (ε + δ + η) (by linarith) (by linarith)
  exact h1.trans (add_le_add h2 le_rfl)
