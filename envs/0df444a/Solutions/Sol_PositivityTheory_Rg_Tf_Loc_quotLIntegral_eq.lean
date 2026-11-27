-- Prove2me | solution 1 for PositivityTheory.Rg.Tf.Loc.quotLIntegral_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:21:00.800129+00:00
-- url     : https://prove2.me/submissions/1c41dd42-dbe4-4d54-a278-45222a656635

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_TwistedFactors_IntegralUnitBaseChange_InvTransposeGLInvTransposeGL
import Theorems.Thm_PositivityTheory_Rg_Tf_Loc_lintegral_normaliser_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Polynomial
open scoped ENNReal
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Tf PositivityTheory.Rg.Tf.Loc
noncomputable section
variable {G : Type*} [Group G]
variable [MeasurableSpace G]
namespace PositivityTheory.Rg.Tf.Loc
theorem _root_.solution [MeasurableMul₂ G] [MeasurableInv G]
    {μG : Measure G} [μG.IsMulLeftInvariant] [SFinite μG]
    {H : Subgroup G} {μH : Measure H} [SFinite μH] [μH.IsInvInvariant]
    {F : G → ℝ≥0∞} (hF : Measurable F) (hFH : ∀ h ∈ H, ∀ g, F (h * g) = F g)
    {ρ : G → ℝ≥0∞} (hρ : IsQuotNormaliser H μH ρ) :
    quotLIntegral μG H μH F = ∫⁻ g, F g * ρ g ∂μG := by
  have hex : ∃ ρ, IsQuotNormaliser H μH ρ := ⟨ρ, hρ⟩
  rw [quotLIntegral, dif_pos hex]
  exact lintegral_normaliser_eq hF hFH hex.choose_spec hρ
end PositivityTheory.Rg.Tf.Loc
