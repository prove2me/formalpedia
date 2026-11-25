-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.TorusLexOrder.norm_torusMono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:44:33.252221+00:00
-- url     : https://prove2.me/submissions/7a9af73e-cec0-407d-99d0-d018b0968fa8

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusLexB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_TorusLexOrder_norm_torusPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
open MeasureTheory ComplexConjugate
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
theorem _root_.solution {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  simp [torusMono, norm_prod, norm_pow, norm_torusPoint]
end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
