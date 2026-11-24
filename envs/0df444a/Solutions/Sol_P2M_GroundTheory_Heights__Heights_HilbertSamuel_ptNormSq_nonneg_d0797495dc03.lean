-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_ptNormSq_nonneg_d0797495dc03
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:44.206147+00:00
-- url     : https://prove2.me/submissions/5866a643-c373-4fe8-a0ff-692fa572afd2

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
theorem _root_.solution (W : Weight L) (n : ℕ) (s : Fin A.n → X → ℂ) (x : X) :
    0 ≤ ptNormSq W n s x := by
  unfold ptNormSq; positivity
end GroundTheory.Heights₂.Heights.HilbertSamuel
