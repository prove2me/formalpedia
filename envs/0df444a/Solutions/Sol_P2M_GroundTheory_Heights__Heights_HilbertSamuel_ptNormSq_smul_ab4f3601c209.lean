-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_smul_ab4f3601c209
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:13.321609+00:00
-- url     : https://prove2.me/submissions/bcc40173-8a02-4e02-be85-ff705f9d27c9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanNorms

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
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution (W : Weight L) (n : ℕ) (c : ℂ) (s : Fin A.n → X → ℂ) (x : X) :
    ptNormSq W n (c • s) x = ‖c‖ ^ 2 * ptNormSq W n s x := by
  simp only [ptNormSq, Pi.smul_apply, smul_eq_mul, norm_mul]
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel
