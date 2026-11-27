-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_sectionL2NormSq_smul_4eab3f040b36
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:05.360704+00:00
-- url     : https://prove2.me/submissions/6ba8c157-d7fb-4cde-8ba3-24416c0343dd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209

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
theorem _root_.solution (W : Weight L) (dV : SmoothVolume A) (n : ℕ) (c : ℂ)
    (s : Fin A.n → X → ℂ) : sectionL2NormSq W dV n (c • s) = ‖c‖ ^ 2 * sectionL2NormSq W dV n s := by
  simp only [sectionL2NormSq, ptNormSq_smul]
  exact integral_const_mul _ _
end GroundTheory.Heights₂.Heights.HilbertSamuel
