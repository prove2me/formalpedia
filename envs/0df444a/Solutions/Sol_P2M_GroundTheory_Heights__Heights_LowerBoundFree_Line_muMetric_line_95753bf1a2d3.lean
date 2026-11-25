-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:55:31.114112+00:00
-- url     : https://prove2.me/submissions/79f5fa48-05c0-4db5-968d-d7aef6aca50a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_norm_muFrameAt_3455c7dba5aa

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
theorem _root_.solution {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : ∃ i, z ⟨(), i⟩ ≠ 0) :
    muMetric (lineHodge II hII) z = 1 := by
  classical
  obtain ⟨i, hi⟩ := hz
  have h : Nonempty (MuFrameAt (lineHodge II hII) z) := ⟨stdFrameAt hi⟩
  rw [muMetric, dif_pos h]
  exact norm_muFrameAt _
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
