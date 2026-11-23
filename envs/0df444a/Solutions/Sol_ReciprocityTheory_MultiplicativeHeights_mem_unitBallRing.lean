-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.mem_unitBallRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:26.589116+00:00
-- url     : https://prove2.me/submissions/4b1fc839-47a2-4b81-8239-9012ea078d20

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_ReciprocityTheory_SemistableReduction_ExistsTorusPointOneLeNormSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MvPolynomial
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {K : Type*} [NormedField K] [IsUltrametricDist K] (x : K) :
    x ∈ unitBallRing K ↔ ‖x‖ ≤ 1 := by
  first
  | (change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
     rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one])
  | (rw [unitBallRing, Valuation.mem_valuationSubring_iff]
     simp [NormedField.valuation_apply, ← NNReal.coe_le_coe])
end ReciprocityTheory.MultiplicativeHeights
