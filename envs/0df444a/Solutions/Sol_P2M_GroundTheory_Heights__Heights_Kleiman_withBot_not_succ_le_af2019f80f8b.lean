-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_withBot_not_succ_le_af2019f80f8b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:30:50.289887+00:00
-- url     : https://prove2.me/submissions/65117938-413b-4ddf-b2c4-10d343574041

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitFilt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsCycleSplitSmall
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PCycleSplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
universe u w
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution {a b : WithBot ℕ∞} (ha : a = ((1 + 1 : ℕ) : WithBot ℕ∞)) (hab : a + 1 ≤ b)
    (hb : b ≤ 2) : False := by
  subst ha
  have := hab.trans hb
  exact absurd this (by decide)
end GroundTheory.Heights₂.Heights.Kleiman
