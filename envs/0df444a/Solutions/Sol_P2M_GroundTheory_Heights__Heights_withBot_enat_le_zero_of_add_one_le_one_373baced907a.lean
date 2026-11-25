-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_withBot_enat_le_zero_of_add_one_le_one_373baced907a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:48.695887+00:00
-- url     : https://prove2.me/submissions/cbbf5c1c-6b19-4ee2-91d0-334437cf899c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCurveNormalisationQuotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : WithBot ℕ∞} (h : x + 1 ≤ 1) : x ≤ 0 := by
  induction x using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    have : e ≤ 0 := by
      induction e using ENat.recTopCoe with
      | top => simp at h'
      | coe k =>
        have hk : k + 1 ≤ 1 := by exact_mod_cast h'
        exact_mod_cast (show k ≤ 0 by omega)
    exact_mod_cast this
end GroundTheory.Heights₂.Heights
