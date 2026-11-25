-- Prove2me | solution 1 for PositivityTheory.SiegelWeilFormula.KFPB.four_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:24:15.951142+00:00
-- url     : https://prove2.me/submissions/55b900d4-4c56-4aed-a631-082914c585e3

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IteratedDerivPolyRealZero
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_IntegrablePolyGauss
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_PolynomialGaussianIntegrals_PolyGaussOfLines

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
theorem _root_.solution (c : ℝ) (h : 𝓢(EuclideanSpace ℝ ι, ℂ)) (ξ : EuclideanSpace ℝ ι) (t : ℝ) :
    𝓕 (gW c h) (t • ξ) = ∫ u, h u * Real.exp (-(c * ‖u‖ ^ 2)) *
      Complex.exp ((-2 * Real.pi * Complex.I * t) * ⟪ξ, u⟫_ℝ) := by
  rw [Real.fourier_eq']
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  simp only [gW, smul_eq_mul, real_inner_smul_right, real_inner_comm u ξ]
  push_cast
  ring_nf
end PositivityTheory.SiegelWeilFormula.KFPB
