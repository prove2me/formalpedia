-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_fb_zero_one_753582a8fa2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:54:33.855745+00:00
-- url     : https://prove2.me/submissions/b8c8d077-75a5-48fb-be25-03485cf523a0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mem_lineF_apply_one_538db3f5cd9a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped Matrix ComplexConjugate
variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])
variable {II hII}
variable {z : (Σ _ : Unit, Fin 2) → ℂ} (d : MuFrameAt (lineHodge II hII) z)
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : fb d 0 1 = 0 := by
  have h := (d.adapted ()).2.2
  have hmem : fb d 0 ∈ lineF := by
    change Submodule.span Ω (Set.range (d.b () ∘ headIdx (show 1 ≤ 2 by decide))) = lineF at h
    rw [← h]
    exact Submodule.subset_span ⟨0, rfl⟩
  exact mem_lineF_apply_one hmem
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
