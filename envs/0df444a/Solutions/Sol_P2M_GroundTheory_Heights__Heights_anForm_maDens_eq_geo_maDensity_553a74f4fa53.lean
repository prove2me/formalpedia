-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_anForm_maDens_eq_geo_maDensity_553a74f4fa53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:42.227274+00:00
-- url     : https://prove2.me/submissions/12e4e30e-b27a-4344-b765-ceafbf47f181

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConePolar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeChartGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLinearNoetherNormalization
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChartGramMA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLogBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConePolar

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
open MvPolynomial MeasureTheory Matrix ComplexSets Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {D : ℕ} (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.ChartRestriction.G.Geo.maDensity φ z :=
  rfl
end GroundTheory.Heights₂.Heights
