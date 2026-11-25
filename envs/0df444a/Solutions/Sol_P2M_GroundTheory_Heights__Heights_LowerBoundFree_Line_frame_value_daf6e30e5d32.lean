-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_value_daf6e30e5d32
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:32:31.438017+00:00
-- url     : https://prove2.me/submissions/9a18b7ae-9f88-49e9-8ff7-59bbd241e51e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_exists_isValueAt_of_pow_mul_mem_aa197e5832ee


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
variable {c : Unit → Fin 2} {f : Ω} {b : Fin 2 → Fin 2 → Ω}
variable {z : (Σ _ : Unit, Fin 2) → ℂ}
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b)
    (hz : z ⟨(), c ()⟩ ≠ 0) (hf : IsUnitAt yLine f z) (q p : Fin 2) :
    ∃ v, IsValueAt yLine (b q p) z v := by
  obtain ⟨n, hn⟩ := frame_regular hfr q p
  exact exists_isValueAt_of_pow_mul_mem (mem_mcPts_line.2 ⟨c (), hz⟩) (segreCoord_line_ne_zero (c ()))
    (fun _ => hz) hf hn
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
