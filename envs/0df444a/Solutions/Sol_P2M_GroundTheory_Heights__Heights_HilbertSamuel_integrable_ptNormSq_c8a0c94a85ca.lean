-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_integrable_ptNormSq_c8a0c94a85ca
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:40:09.571138+00:00
-- url     : https://prove2.me/submissions/75de1b92-9cf8-4d2e-afeb-65a66ae46bee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_continuous_ptNormSq_cb0742b2cef1

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}
variable [MeasurableSpace X] [BorelSpace X]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) (dV : SmoothVolume A) [CompactSpace X] {n : ℕ}
    {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) : Integrable (ptNormSq W n s) dV.μ := by
  have := dV.isProb
  exact (continuous_ptNormSq W hs).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
end GroundTheory.Heights₂.Heights.HilbertSamuel
