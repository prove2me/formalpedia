-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_div_83e03c384ca6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:49.792905+00:00
-- url     : https://prove2.me/submissions/7524c1e0-f734-413e-8025-f40f649ff29d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocRankFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRankFracDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StSemilocChartRatio
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemilocRankFrac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemilocRankFrac_aeval_scale_73809ecd743e

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
theorem _root_.solution (y : (Σ k, ι k) → Ω) {c : K → Ω} (hc : ∀ k, c k ≠ 0) {u w : MRing ι} {a : K → ℕ}
    (hu : IsMultiHomog u a) (hw : IsMultiHomog w a) :
    aeval (fun p => y p * c p.1) u / aeval (fun p => y p * c p.1) w = aeval y u / aeval y w := by
  rw [aeval_scale y c hu, aeval_scale y c hw,
    mul_div_mul_right _ _ (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k))]
end GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac
