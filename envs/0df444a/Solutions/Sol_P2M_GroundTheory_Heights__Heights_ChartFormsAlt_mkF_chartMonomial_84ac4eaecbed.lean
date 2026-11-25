-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartFormsAlt_mkF_chartMonomial_84ac4eaecbed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:36:28.692714+00:00
-- url     : https://prove2.me/submissions/542bf1c9-df34-4e62-8b50-3d3170ad0215

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_ExistsFormOfMemChartRing

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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.ChartFormsAlt
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.ChartFormsAlt
theorem _root_.solution (P : ArithVariety n) (c : (k : ι) → Fin (n k + 1)) (e : ι → ℕ) :
    P.mkF (chartMonomial c e) = ∏ k, P.mkF (X ⟨k, c k⟩) ^ e k := by
  simp [chartMonomial, map_prod, map_pow]
end GroundTheory.Heights₂.Heights.ChartFormsAlt
