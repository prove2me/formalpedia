-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_pow_mul_mem_of_le_a4bda775bd33
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:38.916273+00:00
-- url     : https://prove2.me/submissions/62d85f91-8d4e-4a9b-a071-271fcd28b9d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {Ω : Type} [Field Ω] {ι : Type} (x : ι → Ω) (i : ι)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
theorem _root_.solution {f y : Ω} (hf : f ∈ chartRing ℤ x i) {n n' : ℕ}
    (h : f ^ n * y ∈ chartRing ℤ x i) (hn : n ≤ n') : f ^ n' * y ∈ chartRing ℤ x i := by
  have : f ^ n' * y = f ^ (n' - n) * (f ^ n * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hn]
  rw [this]
  exact mul_mem (pow_mem hf _) h
end GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
