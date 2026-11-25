-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_Line_frame_regular_0c591bfde185
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:35.432462+00:00
-- url     : https://prove2.me/submissions/7fca2ce6-b190-4e12-bfe1-1d9d3453a641

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
theorem _root_.solution (hfr : IsFrameOver yLine (trivialBundle (segreCoord yLine) 2) c f b) (q p : Fin 2) :
    ∃ n : ℕ, f ^ n * b q p ∈ chartRing ℤ (segreCoord yLine) c := by
  obtain ⟨n, hn⟩ := (hfr.2.2.2.2 (b q)).2 ⟨fun q' => if q' = q then 1 else 0, fun q' => ⟨0, by
    show f ^ 0 * (if q' = q then (1 : Ω) else 0) ∈ _
    split_ifs <;> simp⟩, by simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]⟩
  exact ⟨n, by simpa [smul_eq_mul] using mem_trivLat.1 hn p⟩
end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
