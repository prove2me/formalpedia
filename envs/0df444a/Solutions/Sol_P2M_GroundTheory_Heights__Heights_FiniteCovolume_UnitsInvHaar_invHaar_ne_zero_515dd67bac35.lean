-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_UnitsInvHaar_invHaar_ne_zero_515dd67bac35
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:54:22.918256+00:00
-- url     : https://prove2.me/submissions/c32d0cac-f5c9-4b28-aedb-834ea0281e54

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsUnitsInvHaar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PUnitsInvHaar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open MeasureTheory Measure Set
open scoped ENNReal NNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
variable {I : Type*} [Fintype I]
namespace GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
theorem _root_.solution : invHaar I ≠ 0 := by
  intro h
  have h1 : invHaar I univ = 0 := by rw [h]; rfl
  rw [invHaar, map_apply measurable_invUnits MeasurableSet.univ, preimage_univ, weightedVolume,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_eq_zero_iff measurable_invSqWeight] at h1
  have hpos : ∀ b : I → ℂ, invSqWeight b ≠ 0 := fun b =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (ENNReal.inv_ne_zero.2 enorm_ne_top)
  have hF : ∀ᵐ b ∂(volume : Measure (I → ℂ)), False := h1.mono fun b hb => hpos b hb
  exact NeZero.ne (volume : Measure (I → ℂ)) (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hF))
end GroundTheory.Heights₂.Heights.FiniteCovolume.UnitsInvHaar
