-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.gW_int_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:36:05.48421+00:00
-- url     : https://prove2.me/submissions/e0bee34c-2c46-4d65-a08a-b0a22f40859f

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
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (n : ℕ) :
    Integrable (fun v => ‖v‖ ^ n * ‖gW c h v‖) := by
  refine (h.integrable_pow_mul volume n).mono
    (((continuous_norm.pow n).mul (gW_cont c h).norm).aestronglyMeasurable) ?_
  refine ae_of_all _ fun v => ?_
  rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (norm_gW_le hc _ v) (by positivity)
end PositivityTheory.SiegelWeilFormula.KFPB
