-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:33.576815+00:00
-- url     : https://prove2.me/submissions/18068387-d07a-434b-a31b-ae9af8eb0b0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ChartLatSection
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.ChartLatSection
theorem _root_.solution (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1)) (d : ι → ℕ) :
    aeval y (chartMonomial c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [chartMonomial, map_prod]
end GroundTheory.Heights₂.Heights.ChartLatSection
