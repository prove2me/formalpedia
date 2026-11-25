-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_degMu_line_b30aabb74c70
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:15:17.484491+00:00
-- url     : https://prove2.me/submissions/62fa99c5-9d67-4113-b944-d273b300fe07

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_muLine_h_41385f25cd4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_maDensity_eq_zero_of_eventually_4e0ac8d1e147
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_lineData_n_156edb313754


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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution : degMu (lineHodge II hII) = 0 := by
  unfold degMu geomDeg ptsIntegral
  rw [lineData_n]
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have : ∀ y : Fin 1 → ℂ, ∀ w, sheetDensity (mCoordIdeal (lineData II hII).y) hΨ.choose
        (fun _ z => Real.log ((muLine (lineHodge II hII)).h z)) (fun _ => 1) y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [maDensity_eq_zero_of_eventually, mul_zero]
        intro j
        filter_upwards [hγ.choose_spec.2] with y' hy'
        rw [muLine_h (mem_mcPts_line.1 hy'.2.1), Real.log_one]
      · rfl
    simp [this]
  · rfl
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
