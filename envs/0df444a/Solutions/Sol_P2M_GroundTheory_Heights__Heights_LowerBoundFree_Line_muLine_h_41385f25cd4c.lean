-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:07:41.623802+00:00
-- url     : https://prove2.me/submissions/234d8593-53b1-484e-ba53-2eb6c389ea7c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muMetric_line_95753bf1a2d3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineHodge_aMu_944bad2d47be
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_hermOfFun_h_a7599544ae10


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
    (muLine (lineHodge II hII)).h z = 1 := by
  have hom : IsHomogOfDeg (lineHodge II hII).aMu (muMetric (lineHodge II hII)) := by
    intro c w hc
    simp only [lineHodge_aMu, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
    by_cases hw : ∃ i, w ⟨(), i⟩ ≠ 0
    · obtain ⟨i, hi⟩ := hw
      rw [muMetric_line ⟨i, hi⟩, muMetric_line ⟨i, by simp [torusSmul, hc (), hi]⟩]
    · push_neg at hw
      have : torusSmul c w = w := by
        funext p
        obtain ⟨⟨⟩, i⟩ := p
        simp [torusSmul, hw i]
      rw [this]
  obtain ⟨i, hi⟩ := hz
  rw [muLine, hermOfFun_h hom (fun _ => ⟨i, hi⟩) (by rw [muMetric_line ⟨i, hi⟩]; exact one_pos),
    muMetric_line ⟨i, hi⟩]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
