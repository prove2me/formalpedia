-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_withBot_natCast_le_of_add_one_le_3cfdfc22d150
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:40:55.417014+00:00
-- url     : https://prove2.me/submissions/1903b40c-d6a0-4c1b-9722-e8cf42c1a3ac

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLengthParameters
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMRegularElement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLengthLocalizedQuotient
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMLengthParameters

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
open IsLocalRing
universe u
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {k : ℕ} {D : WithBot ℕ∞}
    (h : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ D + 1) : ((k : ℕ) : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe n =>
      have h' : k + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ n)
end GroundTheory.Heights₂.Heights
