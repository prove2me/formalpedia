-- Prove2me | solution 1 for ZetaZeros.D.EllReg.integrable_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:51.920499+00:00
-- url     : https://prove2.me/submissions/4644797a-89b0-471e-99b2-1e6b240e8d14

import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCut
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllipticRegularity_KernDecay

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros ZetaZeros.D ZetaZeros.D.EllReg
open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace ZetaZeros.D.EllReg
theorem _root_.solution {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) (k n : ℕ) :
    Integrable (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) := by
  have hcont : Continuous (fun v => iteratedFDeriv ℝ n f v) :=
    hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  have hc : Continuous (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    (continuous_norm.pow k).mul hcont.norm
  have hs : HasCompactSupport (fun v => ‖v‖ ^ k * ‖iteratedFDeriv ℝ n f v‖) :=
    ((hfc.iteratedFDeriv n).comp_left norm_zero).mul_left
  exact hc.integrable_of_hasCompactSupport hs
end ZetaZeros.D.EllReg
