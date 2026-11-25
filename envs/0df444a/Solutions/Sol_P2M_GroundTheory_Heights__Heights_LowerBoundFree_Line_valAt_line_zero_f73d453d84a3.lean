-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_valAt_line_zero_f73d453d84a3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:44:39.739891+00:00
-- url     : https://prove2.me/submissions/d7be2b2c-3938-4b92-940d-457476e3367e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_mCoordIdeal_yLine_1445442fc678
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_intCast_7d5de349ae80
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_mem_mCoordIdeal_of_aeval_eq_zero_09693c41a4b2


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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution {z : (Σ _ : Unit, Fin 2) → ℂ} : valAt yLine (0 : Ω) z = 0 := by
  classical
  have h : IsValueAt yLine (0 : Ω) z 0 := by simpa using isValueAt_intCast yLine z 0
  unfold valAt
  rw [dif_pos ⟨0, h⟩]
  obtain ⟨d, g, h', hg, hh, hy, heq, hz0, hv⟩ := (⟨0, h⟩ : ∃ v, IsValueAt yLine (0 : Ω) z v).choose_spec
  rw [hv]
  rw [zero_mul] at heq
  have hg0 : g = 0 := by
    have := mem_mCoordIdeal_of_aeval_eq_zero yLine hg heq
    rwa [mCoordIdeal_yLine, Ideal.mem_bot] at this
  simp [hg0]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
