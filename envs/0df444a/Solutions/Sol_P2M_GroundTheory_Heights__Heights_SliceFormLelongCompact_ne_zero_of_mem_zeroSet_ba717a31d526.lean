-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceFormLelongCompact_ne_zero_of_mem_zeroSet_ba717a31d526
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:17:09.252548+00:00
-- url     : https://prove2.me/submissions/f3c6d556-0062-485b-8c29-9d617dacf1f4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLelongRegularise
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsGreenReg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceFormLelongCompactLimit

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold
noncomputable section
open GroundTheory.Heights₂.Heights.SliceFormLelongCompact
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.SliceFormLelongCompact
theorem _root_.solution {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by
  rintro rfl
  have := hx _ hℓ
  simp [linForm] at this
end GroundTheory.Heights₂.Heights.SliceFormLelongCompact
