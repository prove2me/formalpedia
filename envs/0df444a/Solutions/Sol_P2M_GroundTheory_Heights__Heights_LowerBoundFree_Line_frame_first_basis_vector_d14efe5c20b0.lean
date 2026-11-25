-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_first_basis_vector_d14efe5c20b0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:59:14.782781+00:00
-- url     : https://prove2.me/submissions/384c57fb-08fc-48d2-bf3a-a23b7ec905e0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Values
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_LineMu

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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line
theorem _root_.solution (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) :
    ∃ a : Fin 2 → Ω, (∀ q, ∃ n : ℕ, f ^ n * a q ∈ chartRing ℤ (segreCoord yLine) c) ∧
      (Pi.single 0 1 : Fin 2 → Ω) = ∑ q, a q • b q := by
  refine (hfr.2.2.2.2 _).1 ⟨0, ?_⟩
  rw [pow_zero, one_smul]
  refine mem_trivLat.2 fun r => ?_
  by_cases h : r = 0
  · subst h; simp
  · simp [Pi.single_apply, h]
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
