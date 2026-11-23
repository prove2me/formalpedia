-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.WeakAdj.sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:33:32.902781+00:00
-- url     : https://prove2.me/submissions/8368682b-d86a-4fc2-ac04-87d31af811e3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_MinimalSolution
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HormanderLemma

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open scoped InnerProductSpace
variable {E H₁ H₂ : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
namespace ReciprocityTheory.L2DbarEstimates
namespace WeakAdj
theorem _root_.solution {ι : E →ₗ[ℂ] H₁} {t : E →ₗ[ℂ] H₂} {f f' : H₂} {w w' : H₁}
    (h : WeakAdj ι t f w) (h' : WeakAdj ι t f' w') : WeakAdj ι t (f - f') (w - w') := by
  intro g
  rw [inner_sub_right, inner_sub_right, h g, h' g]
end WeakAdj
end ReciprocityTheory.L2DbarEstimates
