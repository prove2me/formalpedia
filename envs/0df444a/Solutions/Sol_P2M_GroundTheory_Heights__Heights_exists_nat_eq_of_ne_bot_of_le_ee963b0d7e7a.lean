-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_exists_nat_eq_of_ne_bot_of_le_ee963b0d7e7a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:40:44.16682+00:00
-- url     : https://prove2.me/submissions/0d1db724-8fae-4622-b054-8e3ad049db6e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDSerre
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMProjDimCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumDepthLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAuslanderBuchsbaumProjDimUpper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegularSequenceLengthLeDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMHeightAddDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMProjDimCriterion

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
open IsLocalRing CategoryTheory RingTheory.Sequence
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {x : WithBot ℕ∞} {d : ℕ} (h0 : x ≠ ⊥) (hle : x ≤ (d : WithBot ℕ∞)) :
    ∃ e : ℕ, x = e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe y =>
    have hy : y ≤ (d : ℕ∞) := by exact_mod_cast hle
    have hyt : y ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top d) hy
    exact ⟨y.toNat, by rw [← ENat.natCast_toNat hyt]; rfl⟩
end GroundTheory.Heights₂.Heights
