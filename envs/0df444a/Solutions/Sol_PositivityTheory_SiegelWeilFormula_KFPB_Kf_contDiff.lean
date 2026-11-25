-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.Kf_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:43:21.122835+00:00
-- url     : https://prove2.me/submissions/e6a47a06-c574-455b-af21-297a9c5a10e4

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines
import Theorems.Thm_PositivityTheory_SiegelWeilFormula_KFPB_gW_int_pow

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
theorem _root_.solution {c : ℝ} (hc : 0 ≤ c) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (N : ℕ) : ContDiff ℝ N (Kf c h) := by
  unfold Kf
  refine ContDiff.mul ?_ ?_
  · exact Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp (contDiff_const.mul (contDiff_norm_sq ℝ)))
  · exact (Real.contDiff_fourier (N := ⊤) (fun n _ => gW_int_pow hc h n)).of_le
      (by exact_mod_cast le_top)
end PositivityTheory.SiegelWeilFormula.KFPB
