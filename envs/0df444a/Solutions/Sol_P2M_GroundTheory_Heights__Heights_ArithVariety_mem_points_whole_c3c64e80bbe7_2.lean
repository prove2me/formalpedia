-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_whole_c3c64e80bbe7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:54:24.116035+00:00
-- url     : https://prove2.me/submissions/764ca452-4d91-4cab-a7b3-a30dbb73caa3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.ArithVariety
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights.ArithVariety
theorem _root_.solution {F : Type*} [CommRing F] {z : Cone n F} (hz : BlockNonzero z) :
    z ∈ (whole n).points F := by
  refine ⟨hz, fun f hf ↦ ?_⟩
  change f ∈ (⊥ : Ideal _) at hf
  rw [Submodule.mem_bot] at hf
  rw [hf, evalCone, eval₂_zero]
end GroundTheory.Heights₂.Heights.ArithVariety
