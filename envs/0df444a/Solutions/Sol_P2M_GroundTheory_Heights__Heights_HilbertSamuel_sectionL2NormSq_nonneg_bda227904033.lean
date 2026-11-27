-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_nonneg_bda227904033
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:56:58.532899+00:00
-- url     : https://prove2.me/submissions/1611a2b1-e54f-4ad4-8d39-7cc107f0d370

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03

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
omit [BorelSpace X]
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (s : Fin A.n → X → ℂ) :
    0 ≤ sectionL2NormSq W dV n s :=
  integral_nonneg fun x => ptNormSq_nonneg W n s x
end GroundTheory.Heights₂.Heights.HilbertSamuel
