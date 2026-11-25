-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_withBot_le_one_of_le_two_20da161cf909
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:06.694804+00:00
-- url     : https://prove2.me/submissions/876c5621-24c4-46f4-9681-94f2a6f4b9cb

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
theorem _root_.solution {a : WithBot ℕ∞} (h2 : a ≤ 2)
    (hne : a ≠ ((1 + 1 : ℕ) : WithBot ℕ∞)) : a ≤ 1 := by
  induction a using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd h2 (by decide)
    | coe n =>
      have h2a : (n : ℕ∞) ≤ 2 := WithBot.coe_le_coe.mp h2
      have h2' : n ≤ 2 := by exact_mod_cast h2a
      have hne' : n ≠ 2 := fun h => hne (by rw [h]; rfl)
      have h1 : (n : ℕ∞) ≤ 1 := by exact_mod_cast (show n ≤ 1 by omega)
      exact WithBot.coe_le_coe.mpr h1
end GroundTheory.Heights₂.Heights.Kleiman
