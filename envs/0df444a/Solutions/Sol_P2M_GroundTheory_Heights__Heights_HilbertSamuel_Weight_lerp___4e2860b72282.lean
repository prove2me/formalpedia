-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_lerp___4e2860b72282
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:57:44.730551+00:00
-- url     : https://prove2.me/submissions/8d1b3aad-bae7-45b3-9f48-dc3cc478b918

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_SectionL2NormSq
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HolLineBundleToAltTransition

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
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}
open GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
variable {L : HolLineBundle A}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
theorem _root_.solution (W₀ W₁ : Weight L) (t : ℝ) :
    (W₀.lerp W₁ t).φ = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.interp W₀.φ W₁.φ t :=
  rfl
end GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
