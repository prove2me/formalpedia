-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_HolLineBundle_sections_eq_sectionSpace_f575eeea46f9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:39.370664+00:00
-- url     : https://prove2.me/submissions/045c2ea6-b7ff-4e3b-8209-afdb6c7f1b3e

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
open GroundTheory.Heights₂.Heights.HilbertSamuel.HolLineBundle
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.HolLineBundle
theorem _root_.solution (L : HolLineBundle A) (n : ℕ) :
    L.sections n = IndefiniteRowSideFullHecke.HilbertSamuel.Bergman.sectionSpace L.toIndefiniteRowSideFullHecke n := by
  ext f
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨a, c, b⟩
  · rintro ⟨a, b, c⟩
    exact ⟨a, c, b⟩
end GroundTheory.Heights₂.Heights.HilbertSamuel.HolLineBundle
