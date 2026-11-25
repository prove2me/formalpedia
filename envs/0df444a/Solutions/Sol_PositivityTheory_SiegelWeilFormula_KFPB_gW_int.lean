-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.gW_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:40.521296+00:00
-- url     : https://prove2.me/submissions/2000ed1d-745e-4cad-b58d-ca6ac22921ab

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_gW_cont
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_norm_gW_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped SchwartzMap InnerProductSpace FourierTransform
open MeasureTheory
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.KFPB
variable {ι : Type} [Fintype ι]
namespace PositivityTheory.SiegelWeilFormula.KFPB
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) : Integrable (gW c h) := h.integrable.mono (gW_cont c h).aestronglyMeasurable (ae_of_all _ fun v => norm_gW_le hc h v)
end PositivityTheory.SiegelWeilFormula.KFPB
